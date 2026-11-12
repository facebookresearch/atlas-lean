/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.FiniteCurrentTightness

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def boundaryCurrentSum (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) : ℝ :=
  ∑' m : EdgeCurrent G,
    if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0


noncomputable def boundaryCurrentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) (m : EdgeCurrent G) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0)


theorem boundaryCurrentSummand_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (m : EdgeCurrent G) :
    0 ≤ if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
      weight G beta J (ofEdgeFun G m) else 0 := by
  split
  · unfold weight
    exact Finset.prod_nonneg fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ e)) _) (Nat.cast_nonneg _)
  · exact le_rfl


theorem summable_boundaryCurrentSummand (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) :
    Summable (fun m : EdgeCurrent G =>
      if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
        weight G beta J (ofEdgeFun G m) else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G beta J)
  by_cases h : (sources G (ofEdgeFun G m)) ∩ interior = ∅ <;> simp [h]


theorem tsum_boundaryCurrentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    ∑' m : EdgeCurrent G, boundaryCurrentRawMass G beta J interior m =
      ENNReal.ofReal (boundaryCurrentSum G beta J interior) := by
  unfold boundaryCurrentRawMass boundaryCurrentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact fun m => boundaryCurrentSummand_nonneg G beta J hbeta hJ interior m
  · exact summable_boundaryCurrentSummand G beta J interior


theorem one_le_boundaryCurrentSum (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    1 ≤ boundaryCurrentSum G beta J interior := by
  unfold boundaryCurrentSum
  have hs := summable_boundaryCurrentSummand G beta J interior
  calc
    1 = (if (sources G (ofEdgeFun G (0 : EdgeCurrent G))) ∩ interior = ∅ then
        weight G beta J (ofEdgeFun G (0 : EdgeCurrent G)) else 0) := by
      rw [if_pos]
      · rw [weight_ofEdgeFun]
        simp
      · simp [sources_zero_current G]
    _ ≤ ∑' m : EdgeCurrent G,
        if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
          weight G beta J (ofEdgeFun G m) else 0 :=
      hs.le_tsum (0 : EdgeCurrent G) (fun m _ =>
        boundaryCurrentSummand_nonneg G beta J hbeta hJ interior m)


noncomputable def boundaryCurrentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    PMF (EdgeCurrent G) :=
  PMF.normalize (boundaryCurrentRawMass G beta J interior)
    (by
      rw [tsum_boundaryCurrentRawMass G beta J hbeta hJ interior]
      exact (ENNReal.ofReal_pos.mpr
        (lt_of_lt_of_le Real.zero_lt_one
          (one_le_boundaryCurrentSum G beta J hbeta hJ interior))).ne')
    (by
      rw [tsum_boundaryCurrentRawMass G beta J hbeta hJ interior]
      exact ENNReal.ofReal_ne_top)


theorem boundaryCurrentPMF_apply (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V)
    (m : EdgeCurrent G) :
    boundaryCurrentPMF G beta J hbeta hJ interior m =
      boundaryCurrentRawMass G beta J interior m *
        (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
  rw [boundaryCurrentPMF, PMF.normalize_apply,
    tsum_boundaryCurrentRawMass G beta J hbeta hJ interior]


noncomputable def boundaryCurrentMeasure (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    ProbabilityMeasure (EdgeCurrent G) :=
  ⟨(boundaryCurrentPMF G beta J hbeta hJ interior).toMeasure, inferInstance⟩


theorem boundaryCurrentMeasure_sources_interior (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (interior : Finset V) :
    (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G))
      {m | (sources G (ofEdgeFun G m)) ∩ interior = ∅} = 1 := by
  change (boundaryCurrentPMF G beta J hbeta hJ interior).toMeasure
    {m | (sources G (ofEdgeFun G m)) ∩ interior = ∅} = 1
  apply (PMF.toMeasure_apply_eq_one_iff _ (Set.to_countable _).measurableSet).2
  intro m hm
  by_contra hsrc
  have hmne : boundaryCurrentPMF G beta J hbeta hJ interior m ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hm
  apply hmne
  rw [boundaryCurrentPMF_apply]
  have hsrc' : (sources G (ofEdgeFun G m)) ∩ interior ≠ ∅ := by
    simpa using hsrc
  simp [boundaryCurrentRawMass, hsrc']

end StatMech.FrontierB
