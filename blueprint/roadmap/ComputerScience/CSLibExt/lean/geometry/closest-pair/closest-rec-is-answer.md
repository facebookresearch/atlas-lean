---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.closestRec_isAnswer
---

# Closest Rec is Answer

On a strip sorted by `y`, every pair whose squared `y` gap is below `δ` is compared. -/
theorem stripScan_lower (δ : 𝕜) (ys : List (𝕜 × 𝕜)) (hs : ys.Pairwise fun a b => a.2 ≤ b.2)
    (a b : 𝕜 × 𝕜) (hab : [a, b] <+ ys) (hgap : (b.2 - a.2) ^ 2 < δ) :
    ∃ d, (stripScan δ ys).ret = some d ∧ d ≤ dist2 a b := by
  induction ys with
  | nil => simp at hab
  | cons p ps ih =>
      simp only [stripScan, ret_bind, ret_pure]
      rcases pair_sublist_cons hab with h | ⟨rfl, hb⟩
      · exact optMin_le_right _ (ih hs.of_cons h)
      · exact optMin_le_left _ (scanFrom_lower δ a ps hs.of_cons
          (fun q hq => List.rel_of_pairwise_cons hs hq) b hb hgap)

/-! ## Divide and conquer

## Depends on

- [Is Answer](is-answer.md)
- [Closest Rec](closest-rec.md)

## Proof depends on

- [Brute Min](brute-min.md)
- [Dist2](dist2.md)
- [Min Dist From](min-dist-from.md)
- [Min Dist From spec](min-dist-from-spec.md)
- [Scan From](scan-from.md)
- [Strip Scan](strip-scan.md)
- [Strip Scan lower](strip-scan-lower.md)
- [Omin](../../data-structures/part-03/sparse-table/omin.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.ClosestPair](../../../../../../sources/v2/CSLibExt.md)
