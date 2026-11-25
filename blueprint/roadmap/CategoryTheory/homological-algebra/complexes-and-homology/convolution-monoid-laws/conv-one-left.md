# Conv one left

Convolution left unit, up to the `zero_add` degree transport.

For `f : HomComplex.Cochain C A n`, casting `conv convOne f` along
`zero_add n` gives `f`, via the one-sided middle interchange
(`tensor_convOne_middle_interchange`), the inner support-collapse of
`tensor (ofHom one) f` (`tensor_one_desc_singleton`), the slides
`ofHom_counit_slide`/`ofHom_one_slide` in `congr_v` form, the graded
expansion `HomologicalComplex.leftUnitor'_inv`, and the `ModuleCat` unitor
assembly (`ιTensorObj_tensorHom`, `ιTensorObj_leftUnitor_hom`, unitor
naturality) with the cast computation `cochain_cast_v`.

No new associativity beyond the existing `conv_assoc`, no
bar-cobar/twisting adjunctions, no derived/Koszul, no operads, no KQ.
