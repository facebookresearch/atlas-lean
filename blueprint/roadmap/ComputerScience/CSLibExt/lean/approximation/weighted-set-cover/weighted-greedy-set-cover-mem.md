---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.weightedGreedySetCover_mem
---

# Weighted Greedy Set Cover mem

Weighted greedy set cover of `U` from the family `F` with costs `w`: take a set meeting `U`
with the least cost per newly covered element, remove it from `U`, repeat; stop when no set meets
`U`. -/
def weightedGreedySetCover (w : Finset α → ℚ) (F : List (Finset α)) (U : Finset α) :
    TimeM ℕ (List (Finset α)) := do
  ✓[F.length + (F.map Finset.card).sum]
  match _h : bestRatioSet w F U with
  | none => pure []
  | some S => do
      let C ← weightedGreedySetCover w F (U \ S)
      pure (S :: C)
termination_by U.card
decreasing_by exact card_sdiff_lt (bestRatioSet_spec _h).2.1

/-! ## The result is a cover from the family

## Depends on

- [Weighted Greedy Set Cover](weighted-greedy-set-cover.md)

## Proof depends on

- [Best Ratio Set](best-ratio-set.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Approximation.WeightedSetCover](../../../../../../sources/v2/CSLibExt.md)
