/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Code.Ising.CorrelationRatio
import Code.Sharpness.TwoReplica

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech
namespace FrontierB

open Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


abbrev EdgeCurrent : Type _ := ↑G.edgeFinset → ℕ


noncomputable def currentRawMass (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : EdgeCurrent G) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if sources G (ofEdgeFun G m) = A then weight G beta J (ofEdgeFun G m) else 0)



theorem currentSummand_nonneg (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) (m : EdgeCurrent G) :
    0 ≤ if sources G (ofEdgeFun G m) = A then weight G beta J (ofEdgeFun G m) else 0 := by
  split
  case isTrue =>
    unfold weight
    exact Finset.prod_nonneg fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hbeta (hJ e)) _) (Nat.cast_nonneg _)
  case isFalse => exact le_rfl


theorem tsum_currentRawMass (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V) :
    ∑' m : EdgeCurrent G, currentRawMass G beta J A m =
      ENNReal.ofReal (currentSum G beta J A) := by
  unfold currentRawMass currentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact fun m => currentSummand_nonneg G beta J hbeta hJ A m
  · exact (summable_norm_currentSum_summand G beta J A).of_norm



noncomputable def currentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) : PMF (EdgeCurrent G) :=
  PMF.normalize (currentRawMass G beta J A)
    (by
      rw [tsum_currentRawMass G beta J hbeta hJ A]
      exact (ENNReal.ofReal_pos.mpr hA).ne')
    (by
      rw [tsum_currentRawMass G beta J hbeta hJ A]
      exact ENNReal.ofReal_ne_top)


theorem currentPMF_apply (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) (m : EdgeCurrent G) :
    currentPMF G beta J hbeta hJ A hA m =
      currentRawMass G beta J A m *
        (ENNReal.ofReal (currentSum G beta J A))⁻¹ := by
  rw [currentPMF, PMF.normalize_apply, tsum_currentRawMass G beta J hbeta hJ A]


theorem currentPMF_apply_eq_zero_of_sources_ne (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (A : Finset V)
    (hA : 0 < currentSum G beta J A) (m : EdgeCurrent G)
    (hm : sources G (ofEdgeFun G m) ≠ A) :
    currentPMF G beta J hbeta hJ A hA m = 0 := by
  rw [currentPMF_apply]
  simp [currentRawMass, hm]



noncomputable def sourcelessCurrentPMF (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) : PMF (EdgeCurrent G) :=
  currentPMF G beta J hbeta hJ ∅ (Ising.acr_currentSum_empty_pos G beta J)



noncomputable def sourcelessCurrentMeasure (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    ProbabilityMeasure (EdgeCurrent G) :=
  ⟨(sourcelessCurrentPMF G beta J hbeta hJ).toMeasure, inferInstance⟩


theorem sourcelessCurrentMeasure_singleton (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (m : EdgeCurrent G) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G)) {m} =
      sourcelessCurrentPMF G beta J hbeta hJ m := by
  exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton m)


theorem sourcelessCurrentMeasure_sources (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    (sourcelessCurrentMeasure G beta J hbeta hJ : Measure (EdgeCurrent G))
      {m | sources G (ofEdgeFun G m) = ∅} = 1 := by
  change (sourcelessCurrentPMF G beta J hbeta hJ).toMeasure
    {m | sources G (ofEdgeFun G m) = ∅} = 1
  apply (PMF.toMeasure_apply_eq_one_iff _ (Set.to_countable _).measurableSet).2
  intro m hm
  by_contra hsrc
  have hmne : sourcelessCurrentPMF G beta J hbeta hJ m ≠ 0 :=
    (PMF.mem_support_iff _ _).1 hm
  have hzero : sourcelessCurrentPMF G beta J hbeta hJ m = 0 :=
    currentPMF_apply_eq_zero_of_sources_ne G beta J hbeta hJ ∅
      (Ising.acr_currentSum_empty_pos G beta J) m hsrc
  exact hmne hzero

end FrontierB
end StatMech
