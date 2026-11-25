# Tensor Hom f heq

Nested tensor-map components are heterogeneously congruent when their two
leaf graded maps are heterogeneously equal.

Rewrite direction: this packages `tensorHom_f_eq_graded` on both sides and
reduces a nested complex-tower comparison to four shallow carrier equalities
plus the two shallow hypotheses `hf` and `hg`.  Abstract contract tests
use it under `eq_of_heq`; concrete Bar/Cobar clients additionally need
propositional leaf equalities.
