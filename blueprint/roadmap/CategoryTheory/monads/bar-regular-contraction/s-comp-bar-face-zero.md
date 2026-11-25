# S comp bar Face zero

Regular-right distinguished zero-face law: `s_n ≫ d₀ = 𝟙`.

At `a : A` let `X = (monadPow T n).obj (L a)` so `B_n a = T.obj X` by `rfl`.
`s` is `η_{B_n} ≫ eqToHom (barObj_obj_succ_eq).symm` by `s_app`.
The `0`-face is `barFaceApp_of_val_zero` which is `rightActionPow`.
By `rightActionPow_eq` for the regular right module `(regular T).functor = T`
and `(regular T).action = T.μ`, this face is
`T.map (eqToHom (monadPow_succ_obj_eq)) ≫ T.μ_X`.
The generic `eqToHom_map` gives `T.map (eqToHom _) = eqToHom (congrArg T.obj _)`.
The bar successor comparison `barObj_obj_succ_eq L n a` is
`congrArg T.obj (monadPow_succ_obj_eq n _)` by `rfl`
(`monadPow_succ_obj_eq = monadPow_obj_T_comm`). Hence the composite is
`η_{T X} ≫ eqToHom.symm ≫ eqToHom ≫ μ_X`.
Cancelling by `eqToHom_symm_comp_eq` yields `η_{T X} ≫ μ_X`, which is `𝟙` by
`T.left_unit`.
