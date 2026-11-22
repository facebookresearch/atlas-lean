# Weighted-average identity

**Weighted-average identity** (algebraic) for the mole fractions of a sum `n₁ + n₂` of
amount families over the same species (over `Chemistry.Amounts.moleFraction`): each is the
average of the two mole fractions weighted by the totals `N₁ = ∑ j, n₁ j` and `N₂ = ∑ j, n₂ j`.
Only `N₁ ≠ 0` and `N₂ ≠ 0` are assumed, so this is not a physical mixing or convexity claim:
totals `-1` and `2` give weights `-1` and `2`, and when `N₁ + N₂ = 0` both sides are `0` by
Lean's division convention. Mixing two solutions with no reaction adds their amounts; for
positive totals see `moleFraction_mix_convex`.
