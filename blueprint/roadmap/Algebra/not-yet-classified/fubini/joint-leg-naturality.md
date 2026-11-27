# Joint Leg naturality

Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i i' j j' : ℕ`, `f : i ⟶ i'`, and `g : j ⟶ j'`.
The map on the two indices followed by the leg at `(i', j')` equals the leg at `(i, j)`:

```text
((F.map f).app j ≫ (F.obj i').map g) ≫ jointLeg F i' j' = jointLeg F i j
```
