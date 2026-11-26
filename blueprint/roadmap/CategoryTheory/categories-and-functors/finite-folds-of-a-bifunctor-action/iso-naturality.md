# Fold isomorphisms preserve a commuting prefix square

For a bifunctor `F : C ⥤ D ⥤ C`, let `f : P → P′`, `g : Q → Q′`,
`e : P ≅ Q` and `e′ : P′ ≅ Q′` satisfy `f ≫ e′.hom = e.hom ≫ g`.
Fix ordered families `M`, `N : Fin n → D` and isomorphisms
`h(j) : M(j) ≅ N(j)`. The corresponding square between the folds
commutes: the folded map of `f` followed by the fold isomorphism from
`e′` equals the fold isomorphism from `e` followed by the folded map of `g`.
