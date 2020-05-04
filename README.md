LTL (Linear Temporal Logic) in Coq
=======

“Temporal Logic is suggested as an appropriate tool for formalizing the semantics of concurrent programs.”  
─Amir Pnueli


This repository contains a simple formalization of many LTL concepts and theorems.

I used CoqIde 8.11.


The script contains:

    * Path formulas definition
    * Path definition
    * LTL semantic definition (π ⊨ ф)
    * Many LTL equivalences like:
        * π ⊨ ф -> ~ π ⊨ negP ф
        * π ⊨ X (ф₁ ∨ ф₂) <-> π ⊨ X ф₁ ∨ X ф₂
        * π ⊨ X (ф₁ ∧ ф₂) <-> π ⊨ X ф₁ ∧ X ф₂
        * π ⊨ X (ф₁ U ф₂) <-> π ⊨ X ф₁ U X ф₂
        * π ⊨ F (ф₁ ∨ ф₂) <-> π ⊨ F ф₁ ∨ F ф₂
        * π ⊨ G (ф₁ ∧ ф₂) <-> π ⊨ G ф₁ ∧ G ф₂
        * π ⊨ F (F ф) <-> π ⊨ F ф
        * π ⊨ G (G ф) <-> π ⊨ G ф
    * Two important theorems:
        * π ⊨ ф₁ U ф₂ <-> π ⊨ ф₂ ∨ (ф₁ ∧ X (ф₁ U ф₂))
        * π ⊨ ф₁ V ф₂ <-> π ⊨ ф₂ ∧ (ф₁ ∨ (X (ф₁ V ф₂)))


