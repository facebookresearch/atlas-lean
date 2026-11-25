# Bar Change Data Hom comp

Data-level composition law for same-carrier monad change.

For `h : T ⟶ S`, `k : S ⟶ U`, the composite

`(barDataRestrictCompIso h k R L).hom ≫ barChangeDataHom h (restrict k R) (restrict k L) ≫
  barChangeDataHom k R L`

coincides with `barChangeDataHom (h ≫ k) R L`.

The proof is extensional degreewise and reduces to
`barDataRestrictCompIso_hom_app` (the restriction iso is identity degreewise)
and `barChangeMap_comp`.
