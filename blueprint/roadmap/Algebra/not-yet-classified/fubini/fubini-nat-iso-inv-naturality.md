# Fubini Nat Iso inv naturality

For `F G : ℕ ⥤ ℕ ⥤ GrpCat` and a natural transformation `a : F ⟶ G`, the
inverse Fubini map commutes with the induced map on double quotients. Starting in
opposite order, use the flipped transformation before applying the inverse:

```text
iteratedColimitFunctor.map ((flipFunctor ℕ ℕ GrpCat).map a) ≫ (fubiniIso G).inv =
  (fubiniIso F).inv ≫ iteratedColimitFunctor.map a
```
