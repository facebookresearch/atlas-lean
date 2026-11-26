# Fubini Iso inv leg

For `F : ℕ ⥤ ℕ ⥤ GrpCat` and `i j : ℕ`, the inverse map takes the transposed
pair leg of `F.flip` back to the chosen pair leg of `F`:

```text
jointLeg F.flip j i ≫ (fubiniIso F).inv = jointLeg F i j
```
