/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SpinWeightedTarget









namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_prod_scaleEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ)
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    (∏ f ∈ F, ons_scaleEdgeWeight weight edge t f) =
      if edge ∈ F then t * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | @insert f F hf ih =>
      by_cases hfe : f = edge
      · subst f
        rw [Finset.prod_insert hf, Finset.prod_insert hf, ih]
        simp [ons_scaleEdgeWeight, hf]
        ring
      · rw [Finset.prod_insert hf, Finset.prod_insert hf, ih]
        have hef : edge ≠ f := Ne.symm hfe
        by_cases he : edge ∈ F
        · simp [ons_scaleEdgeWeight, hfe, hef, he]
          ring
        · simp [ons_scaleEdgeWeight, hfe, hef, he]

noncomputable def ons_weightedSpinEdgeCoefficient
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (edge : Sym2 (ZMod L × ZMod L)) : ℂ :=
  ∑ F ∈ (evenSubgraphs (onsTorusGraph L)).filter (edge ∈ ·),
    (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
      ∏ f ∈ F, weight f

theorem ons_weightedSpinCharacterSum_scaleEdge
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (edge : Sym2 (ZMod L × ZMod L)) (t : ℂ) :
    ons_weightedSpinCharacterSum L
        (ons_scaleEdgeWeight weight edge t) a b =
      ons_weightedSpinCharacterSum L
          (ons_scaleEdgeWeight weight edge 0) a b +
        t * ons_weightedSpinEdgeCoefficient L weight a b edge := by
  unfold ons_weightedSpinCharacterSum ons_weightedSpinEdgeCoefficient
  simp_rw [ons_prod_scaleEdgeWeight]
  calc
    (∑ F ∈ evenSubgraphs (onsTorusGraph L),
        (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
          if edge ∈ F then t * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f) =
      ∑ F ∈ evenSubgraphs (onsTorusGraph L), (
        ((ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
          if edge ∈ F then 0 * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f) +
        t * (if edge ∈ F then
          (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
            ∏ f ∈ F, weight f else 0)) := by
      apply Finset.sum_congr rfl
      intro F hF
      by_cases he : edge ∈ F <;> simp [he] <;> ring
    _ = (∑ F ∈ evenSubgraphs (onsTorusGraph L),
        (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
          if edge ∈ F then 0 * ∏ f ∈ F, weight f else ∏ f ∈ F, weight f) +
        t * ∑ F ∈ (evenSubgraphs (onsTorusGraph L)).filter (edge ∈ ·),
          (ons_spinCharacter a b (ons_evenHomology L F) : ℂ) *
            ∏ f ∈ F, weight f := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro F hF
      by_cases he : edge ∈ F <;> simp [he]

end StatMech.Onsager
