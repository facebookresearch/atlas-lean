# Iterated Colimit map fac

For `F G : ℕ ⥤ ℕ ⥤ GrpCat`, a natural transformation `a : F ⟶ G`, and `i j : ℕ`,
the induced map on the chosen double quotients factors on each pair leg through
`(a.app i).app j`:

```text
jointLeg F i j ≫ iteratedColimitFunctor.map a = (a.app i).app j ≫ jointLeg G i j
```
