# Fubini Iso naturality

For `F G : ℕ ⥤ ℕ ⥤ GrpCat` and a natural transformation `a : F ⟶ G`, the
forward Fubini map commutes with the induced map on double quotients. The map on the
opposite-order quotients is induced by the flipped transformation:

```text
iteratedColimitFunctor.map a ≫ (fubiniIso G).hom =
  (fubiniIso F).hom ≫ iteratedColimitFunctor.map ((flipFunctor ℕ ℕ GrpCat).map a)
```
