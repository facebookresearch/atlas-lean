/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.FiniteNormalizedSwitching
import Code.Sharpness.DeltaBound

open MeasureTheory
open scoped ENNReal symmDiff

namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def sourceCurrentPairPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B) :
    PMF (EdgeCurrent G × EdgeCurrent G) :=
  (currentPMF G beta J hbeta hJ A hA).bind fun m =>
    (currentPMF G beta J hbeta hJ B hB).map (Prod.mk m)


theorem sourceCurrentPairPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B)
    (m n : EdgeCurrent G) :
    sourceCurrentPairPMF G beta J hbeta hJ A B hA hB (m, n) =
      currentPMF G beta J hbeta hJ A hA m *
        currentPMF G beta J hbeta hJ B hB n := by
  rw [sourceCurrentPairPMF, PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single n]
    · simp
    · intro n' hn'
      simp [Ne.symm hn']
  · intro m' hm'
    simp [PMF.map_apply, Ne.symm hm']



theorem sourceCurrentPairPMF_toMeasure_eq_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B) :
    (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB).toMeasure =
      (currentPMF G beta J hbeta hJ A hA).toMeasure.prod
        (currentPMF G beta J hbeta hJ B hB).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨m, n⟩
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    sourceCurrentPairPMF_apply]
  rw [show ({(m, n)} : Set (EdgeCurrent G × EdgeCurrent G)) =
      ({m} : Set (EdgeCurrent G)) ×ˢ ({n} : Set (EdgeCurrent G)) by
        exact Set.singleton_prod_singleton.symm,
    Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]



def sourcePairSuperpositionEvent
    (P : Current V → Prop) : Set (EdgeCurrent G × EdgeCurrent G) :=
  {pq | P (ofEdgeFun G (fun e => pq.1 e + pq.2 e))}

noncomputable local instance finitePairPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p

private noncomputable def sourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) : ℝ :=
  (if sources G (ofEdgeFun G pq.1) = A then
      weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = B then
      weight G beta J (ofEdgeFun G pq.2) else 0) *
    (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

private theorem sourcePairRealSummand_nonneg
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) :
    0 ≤ sourcePairRealSummand G beta J A B P pq := by
  unfold sourcePairRealSummand
  split <;> split <;> split <;> simp_all only [mul_zero, zero_mul, mul_one]
  all_goals first
    | exact mul_nonneg
        (Ising.acw_weight_nonneg G beta J hbeta hJ _)
        (Ising.acw_weight_nonneg G beta J hbeta hJ _)
    | positivity

private theorem summable_sourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] :
    Summable (sourcePairRealSummand G beta J A B P) := by
  simpa only [sourcePairRealSummand] using
    Sharpness.summable_gatedSourcePairSummand G beta J A B P

private theorem tsum_sourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] :
    ∑' pq, sourcePairRealSummand G beta J A B P pq =
      gatedSourcePairSum G beta J A B P := by
  rfl




theorem sourceCurrentPairPMF_superpositionEvent
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V)
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B)
    (P : Current V → Prop) [DecidablePred P] :
    (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB).toMeasure
        (sourcePairSuperpositionEvent G P) =
      ENNReal.ofReal (normalizedGatedSourcePairSum G beta J A B P) := by
  rw [PMF.toMeasure_apply_eq_tsum]
  let zA := currentSum G beta J A
  let zB := currentSum G beta J B
  let z : ℝ≥0∞ := (ENNReal.ofReal zA * ENNReal.ofReal zB)⁻¹
  have hpoint : ∀ pq : EdgeCurrent G × EdgeCurrent G,
      (sourcePairSuperpositionEvent G P).indicator
          (sourceCurrentPairPMF G beta J hbeta hJ A B hA hB) pq =
        ENNReal.ofReal (sourcePairRealSummand G beta J A B P pq) * z := by
    rintro ⟨m, n⟩
    by_cases hP : P (ofEdgeFun G (fun e => m e + n e))
    · rw [Set.indicator_of_mem]
      · rw [sourceCurrentPairPMF_apply, currentPMF_apply, currentPMF_apply]
        unfold currentRawMass
        by_cases hm : sources G (ofEdgeFun G m) = A <;>
          by_cases hn : sources G (ofEdgeFun G n) = B <;>
          simp [hm, hn, hP, sourcePairRealSummand, z,
            ENNReal.ofReal_mul,
            Ising.acw_weight_nonneg G beta J hbeta hJ]
        all_goals dsimp only [zA, zB]
        all_goals rw [ENNReal.mul_inv
          (Or.inl (ENNReal.ofReal_pos.mpr hA).ne')
          (Or.inl ENNReal.ofReal_ne_top)]
        all_goals ac_rfl
      · exact hP
    · rw [Set.indicator_of_notMem]
      · simp [sourcePairRealSummand, hP]
      · exact hP
  rw [tsum_congr hpoint, ENNReal.tsum_mul_right]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (sourcePairRealSummand_nonneg G beta J hbeta hJ A B P)
    (summable_sourcePairRealSummand G beta J A B P)]
  rw [tsum_sourcePairRealSummand]
  unfold normalizedGatedSourcePairSum
  rw [ENNReal.ofReal_div_of_pos (mul_pos hA hB),
    ENNReal.ofReal_mul hA.le]
  dsimp only [zA, zB, z]
  rw [ENNReal.div_eq_inv_mul]
  ac_rfl




theorem sourceCurrentPairPMF_switching
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) {u v : V} (huv : u ≠ v)
    (P : Current V → Prop) [DecidablePred P]
    (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
    (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
    (hA : 0 < currentSum G beta J A)
    (hzero : 0 < currentSum G beta J ∅) :
    ENNReal.ofReal
        (currentSum G beta J (A ∆ ({u, v} : Finset V)) *
          currentSum G beta J ({u, v} : Finset V)) *
      (sourceCurrentPairPMF G beta J hbeta hJ
        (A ∆ ({u, v} : Finset V)) {u, v} hAu huvSum).toMeasure
          (sourcePairSuperpositionEvent G P) =
    ENNReal.ofReal
        (currentSum G beta J A * currentSum G beta J ∅) *
      (sourceCurrentPairPMF G beta J hbeta hJ
        A ∅ hA hzero).toMeasure
          (sourcePairSuperpositionEvent G
            (fun m => P m ∧ CurrentConnected G m u v)) := by
  rw [sourceCurrentPairPMF_superpositionEvent,
    sourceCurrentPairPMF_superpositionEvent]
  rw [← ENNReal.ofReal_mul (mul_pos hAu huvSum).le,
    ← ENNReal.ofReal_mul (mul_pos hA hzero).le]
  exact congrArg ENNReal.ofReal
    (normalizedGatedSourcePairSum_switching G beta J A huv P
      hAu huvSum hA hzero)

end StatMech.FrontierB
