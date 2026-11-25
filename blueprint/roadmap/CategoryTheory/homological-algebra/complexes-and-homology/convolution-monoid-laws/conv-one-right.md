# Conv one right

Convolution right unit, up to the `add_zero` degree transport.

For `f : HomComplex.Cochain C A n`, casting `conv f convOne` along
`add_zero n` gives `f`, via the one-sided middle interchange
(`tensor_f_convOne_middle_interchange`), the inner support-collapse of
`tensor f (ofHom one)` (`tensor_desc_singleton_one` with explicit
`(0 * r).negOnePow` clearance), the slides `ComonObj.comul_counit`/
`MonObj.mul_one` in `congr_v` form, the graded expansion
`HomologicalComplex.rightUnitor'_inv`, and the `ModuleCat` unitor assembly
(`ιTensorObj_tensorHom`, `ιTensorObj_rightUnitor_hom`, right-unitor
naturality) with the cast computation `cochain_cast_v`.

Order check: the survivor is `(r, 0)` (not `(0, r)`), since `i₁ + i₂ = r`
with `i₂ = 0` forces `i₁ = r`; the sign is `(0 * i₁).negOnePow` (second factor
has degree `0`). Cast check: the public transport is `add_zero n`
(`n + 0 = n`), matching `conv f convOne : Cochain C A (n + 0)`.

No new associativity beyond the existing `conv_assoc`, no
bar-cobar/twisting adjunctions, no derived/Koszul, no operads, no KQ.
