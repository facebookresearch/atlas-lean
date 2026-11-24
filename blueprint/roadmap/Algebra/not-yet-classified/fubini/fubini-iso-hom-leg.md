# Fubini Iso hom leg

For `F : ℕ ⥤ ℕ ⥤ GrpCat` and `i j : ℕ`, the forward map takes the chosen
pair leg of `F` to the transposed pair leg of `F.flip`:

```text
jointLeg F i j ≫ (fubiniIso F).hom = jointLeg F.flip j i
```
