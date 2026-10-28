/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorCache

/-! Full rational short constituents retain the original code labels of all sparse actual roots. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every actual pair coordinate is the sum over every bounded original support address. -/
def generatedFeasibleContainingZeroOutsideAnchorPairQ (k : Fin 4) (s : Fin 2) (p : Fin 276) : ℚ :=
  ∑ n : Fin 120, match generatedFeasibleContainingZeroOutsideAnchorRoot k n with
    | Sum.inl (a, q) => if s = a ∧ p = q then
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient k n : ℚ) else 0
    | Sum.inr _ => 0

/-- Original encoder labels give every octad coordinate, including coordinates outside the cache. -/
def generatedFeasibleContainingZeroOutsideAnchorOctadQ
    (k : Fin 4) (d : Fin 4096) (e : Fin 64) : ℚ :=
  ∑ n : Fin 120, match generatedFeasibleContainingZeroOutsideAnchorRoot k n with
    | Sum.inl _ => 0
    | Sum.inr (j, f) => if d = generatedFeasibleContainingZeroOutsideAnchorCode j ∧ e = f then
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient k n : ℚ) else 0

/-- The entire actual preferred short catalogue is represented, with odd coefficients exactly zero. -/
def generatedFeasibleContainingZeroOutsideAnchorShortQ (k : Fin 4) : GriessShortIndex → ℚ
  | Sum.inl (s, p) => generatedFeasibleContainingZeroOutsideAnchorPairQ k s p
  | Sum.inr (Sum.inl (o, e)) =>
      generatedFeasibleContainingZeroOutsideAnchorOctadQ k (golayOctadLabel o) e
  | Sum.inr (Sum.inr _) => 0

private theorem label_eq_code (j : Fin 14) (o : Fin 759) :
    golayOctadLabel o = generatedFeasibleContainingZeroOutsideAnchorCode j ↔
      o = generatedFeasibleContainingZeroOutsideAnchorOctad j := by
  constructor
  · intro h
    apply (golayOctads.orderIsoOfFin golayOctads_card).injective
    apply Subtype.ext
    change golayOctadLabel o = golayOctadLabel (generatedFeasibleContainingZeroOutsideAnchorOctad j)
    rw [generatedFeasibleContainingZeroOutsideAnchorOctad_label]
    exact h
  · rintro rfl
    exact generatedFeasibleContainingZeroOutsideAnchorOctad_label j

/-- The rational packet is exactly the entire actual short sum; every original label is retained. -/
theorem generatedFeasibleContainingZeroOutsideAnchorShortQ_sum (k : Fin 4) :
    (fun r => (generatedFeasibleContainingZeroOutsideAnchorShortQ k r : ℝ)) =
      ∑ n : Fin 120,
        (generatedFeasibleContainingZeroOutsideAnchorCoefficient k n : ℝ) •
          Pi.single (generatedFeasibleContainingZeroOutsideAnchorIndex
            (generatedFeasibleContainingZeroOutsideAnchorRoot k n)) (1 : ℝ) := by
  funext r
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedFeasibleContainingZeroOutsideAnchorShortQ,
      generatedFeasibleContainingZeroOutsideAnchorPairQ, Rat.cast_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n _
    cases h : generatedFeasibleContainingZeroOutsideAnchorRoot k n with
    | inl z =>
      rcases z with ⟨a, q⟩
      simp only [h, generatedFeasibleContainingZeroOutsideAnchorIndex, Pi.single_apply,
        Sum.inl.injEq, Prod.mk.injEq]
      by_cases hs : s = a <;> by_cases hp : p = q <;> simp [hs, hp]
    | inr z =>
      simp [h, generatedFeasibleContainingZeroOutsideAnchorIndex, Pi.single_apply]
  · simp only [generatedFeasibleContainingZeroOutsideAnchorShortQ,
      generatedFeasibleContainingZeroOutsideAnchorOctadQ, Rat.cast_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n _
    cases h : generatedFeasibleContainingZeroOutsideAnchorRoot k n with
    | inl z =>
      simp [h, generatedFeasibleContainingZeroOutsideAnchorIndex, Pi.single_apply]
    | inr z =>
      rcases z with ⟨j, f⟩
      simp only [h, generatedFeasibleContainingZeroOutsideAnchorIndex, Pi.single_apply,
        Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, label_eq_code]
      by_cases ho : o = generatedFeasibleContainingZeroOutsideAnchorOctad j <;>
        by_cases he : e = f <;> simp [ho, he]
  · simp only [generatedFeasibleContainingZeroOutsideAnchorShortQ,
      Rat.cast_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro n _
    cases h : generatedFeasibleContainingZeroOutsideAnchorRoot k n <;>
      simp [h, generatedFeasibleContainingZeroOutsideAnchorIndex, Pi.single_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
