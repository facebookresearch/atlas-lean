# The DG Yoneda lemma

**The DG Yoneda lemma**, degreewise: morphisms of degree `n` of right DG modules
`Hom(-, X) ⟶ F` are the elements of `F(X)` of degree `n`.  A morphism `η` goes to `η_X(1_X)`
(`MathlibExt.DGSource.dgRepresentableHomEquiv_apply`), and an element `x` goes to the morphism whose component
at `Y` sends `g : Y ⟶ X` of degree `p` to `(-1) ^ (p * n) • F(g)(x)`
(`MathlibExt.DGSource.dgApp_dgRepresentableHomEquiv_symm_v`).
