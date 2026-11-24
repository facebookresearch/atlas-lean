# The Yoneda lemma for right DG modules

DG natural transformations `Hom(-, X) ⟶ F` are the
closed degree-zero elements of `F(X)`.  A transformation goes to the image of the identity of `X`
under its component at `X` (`MathlibExt.DGSource.dgYonedaEquiv_apply_coe`), and a closed element `x` goes to
the transformation sending `g : Y ⟶ X` to `F(g)(x)` (`MathlibExt.DGSource.dgApp_dgYonedaEquiv_symm_v`).
