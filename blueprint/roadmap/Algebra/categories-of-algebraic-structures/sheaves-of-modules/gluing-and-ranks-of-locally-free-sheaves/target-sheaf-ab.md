# Underlying abelian sheaf of a module sheaf

Let `X : TopCat.{u}`, `R` be a ring sheaf of carrier universe `u`, and `G : SheafOfModules.{u}
R`. The sheaf `targetSheafAb G : TopCat.Sheaf Ab X` has presheaf `G.val.presheaf` and the
sheaf condition supplied by `G`. It forgets the module scalar action while retaining the
additive sections and restrictions.
