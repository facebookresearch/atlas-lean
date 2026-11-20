/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.FiniteBoundarySwitching

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance boundarySourceLawPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p


noncomputable def boundarySourceCurrentRawMass
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) (m : EdgeCurrent G) : ℝ≥0∞ :=
  ENNReal.ofReal
    (if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0)

theorem boundarySourceCurrentSummand_nonneg
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V) (m : EdgeCurrent G) :
    0 ≤ if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0 := by
  split
  · exact Ising.acw_weight_nonneg G beta J hbeta hJ _
  · exact le_rfl

theorem summable_boundarySourceCurrentSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) :
    Summable (fun m : EdgeCurrent G =>
      if sources G (ofEdgeFun G m) ∩ interior = internalSources then
        weight G beta J (ofEdgeFun G m)
      else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_norm_weight_ofEdgeFun G beta J)
  by_cases h : sources G (ofEdgeFun G m) ∩ interior = internalSources <;>
    simp [h]

theorem tsum_boundarySourceCurrentRawMass
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V) :
    ∑' m : EdgeCurrent G,
        boundarySourceCurrentRawMass G beta J interior internalSources m =
      ENNReal.ofReal
        (boundarySourceCurrentSum G beta J interior internalSources) := by
  unfold boundarySourceCurrentRawMass boundarySourceCurrentSum
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · exact boundarySourceCurrentSummand_nonneg
      G beta J hbeta hJ interior internalSources
  · exact summable_boundarySourceCurrentSummand
      G beta J interior internalSources


noncomputable def boundarySourceCurrentPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta J interior internalSources) :
    PMF (EdgeCurrent G) :=
  PMF.normalize
    (boundarySourceCurrentRawMass G beta J interior internalSources)
    (by
      rw [tsum_boundarySourceCurrentRawMass
        G beta J hbeta hJ interior internalSources]
      exact (ENNReal.ofReal_pos.mpr hpos).ne')
    (by
      rw [tsum_boundarySourceCurrentRawMass
        G beta J hbeta hJ interior internalSources]
      exact ENNReal.ofReal_ne_top)

theorem boundarySourceCurrentPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources : Finset V)
    (hpos : 0 < boundarySourceCurrentSum G beta J interior internalSources)
    (m : EdgeCurrent G) :
    boundarySourceCurrentPMF G beta J hbeta hJ interior internalSources hpos m =
      boundarySourceCurrentRawMass G beta J interior internalSources m *
        (ENNReal.ofReal
          (boundarySourceCurrentSum G beta J interior internalSources))⁻¹ := by
  rw [boundarySourceCurrentPMF, PMF.normalize_apply,
    tsum_boundarySourceCurrentRawMass
      G beta J hbeta hJ interior internalSources]



noncomputable def boundarySourceCurrentPairPMF
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources) :
    PMF (EdgeCurrent G × EdgeCurrent G) :=
  (boundarySourceCurrentPMF G beta J hbeta hJ
      interior internalSources hfirst).bind fun m =>
    (currentPMF G beta J hbeta hJ exactSecondSources hsecond).map
      (Prod.mk m)

theorem boundarySourceCurrentPairPMF_apply
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources)
    (m n : EdgeCurrent G) :
    boundarySourceCurrentPairPMF G beta J hbeta hJ interior
        internalSources exactSecondSources hfirst hsecond (m, n) =
      boundarySourceCurrentPMF G beta J hbeta hJ
          interior internalSources hfirst m *
        currentPMF G beta J hbeta hJ exactSecondSources hsecond n := by
  rw [boundarySourceCurrentPairPMF, PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single n]
    · simp
    · intro n' hn'
      simp [Ne.symm hn']
  · intro m' hm'
    simp [PMF.map_apply, Ne.symm hm']



theorem boundarySourceCurrentPairPMF_toMeasure_eq_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources) :
    (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
      internalSources exactSecondSources hfirst hsecond).toMeasure =
      (boundarySourceCurrentPMF G beta J hbeta hJ
        interior internalSources hfirst).toMeasure.prod
      (currentPMF G beta J hbeta hJ exactSecondSources hsecond).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨m, n⟩
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    boundarySourceCurrentPairPMF_apply]
  rw [show ({(m, n)} : Set (EdgeCurrent G × EdgeCurrent G)) =
      ({m} : Set (EdgeCurrent G)) ×ˢ ({n} : Set (EdgeCurrent G)) by
        exact Set.singleton_prod_singleton.symm,
    Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]

private noncomputable def boundarySourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) : ℝ :=
  (if sources G (ofEdgeFun G pq.1) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G pq.1) else 0) *
    (if sources G (ofEdgeFun G pq.2) = exactSecondSources then
      weight G beta J (ofEdgeFun G pq.2) else 0) *
    (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

private theorem boundarySourcePairRealSummand_nonneg
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (pq : EdgeCurrent G × EdgeCurrent G) :
    0 ≤ boundarySourcePairRealSummand G beta J interior internalSources
      exactSecondSources P pq := by
  unfold boundarySourcePairRealSummand
  split <;> split <;> split <;>
    simp_all only [mul_zero, zero_mul, mul_one]
  all_goals first
    | exact mul_nonneg
        (Ising.acw_weight_nonneg G beta J hbeta hJ _)
        (Ising.acw_weight_nonneg G beta J hbeta hJ _)
    | exact le_rfl

private theorem summable_boundarySourcePairRealSummand
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P] :
    Summable (boundarySourcePairRealSummand G beta J interior
      internalSources exactSecondSources P) := by
  let f : Finset V → (EdgeCurrent G × EdgeCurrent G) → ℝ := fun A pq =>
    if A ∩ interior = internalSources then
      (if sources G (ofEdgeFun G pq.1) = A then
        weight G beta J (ofEdgeFun G pq.1) else 0) *
      (if sources G (ofEdgeFun G pq.2) = exactSecondSources then
        weight G beta J (ofEdgeFun G pq.2) else 0) *
      (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)
    else 0
  have hf : ∀ A : Finset V, Summable (f A) := by
    intro A
    by_cases hA : A ∩ interior = internalSources
    · simpa only [f, hA, if_true] using
        Sharpness.summable_gatedSourcePairSummand
          G beta J A exactSecondSources P
    · simp only [f, hA, if_false]
      exact summable_zero
  have hfinite : ∀ s : Finset (Finset V),
      Summable (fun pq => ∑ A ∈ s, f A pq) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (summable_zero : Summable
            (fun _ : EdgeCurrent G × EdgeCurrent G => (0 : ℝ)))
    | @insert A s hAs ih =>
        simpa [Finset.sum_insert hAs] using (hf A).add ih
  have hall : Summable (fun pq => ∑ A : Finset V, f A pq) := by
    simpa using hfinite (Finset.univ : Finset (Finset V))
  apply hall.congr
  intro pq
  rw [show (∑ A : Finset V, f A pq) =
      f (sources G (ofEdgeFun G pq.1)) pq by
    rw [Finset.sum_eq_single (sources G (ofEdgeFun G pq.1))]
    · intro A _ hA
      by_cases hsector : A ∩ interior = internalSources
      · simp [f, hsector, Ne.symm hA]
      · simp [f, hsector]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim]
  by_cases hfirst :
      sources G (ofEdgeFun G pq.1) ∩ interior = internalSources <;>
    by_cases hsecond :
      sources G (ofEdgeFun G pq.2) = exactSecondSources <;>
    by_cases hP : P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) <;>
    simp [f, boundarySourcePairRealSummand, hfirst, hsecond, hP]



theorem boundarySourceCurrentPairPMF_superpositionEvent
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources exactSecondSources : Finset V)
    (hfirst : 0 < boundarySourceCurrentSum
      G beta J interior internalSources)
    (hsecond : 0 < currentSum G beta J exactSecondSources)
    (P : Current V → Prop) [DecidablePred P] :
    (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
      internalSources exactSecondSources hfirst hsecond).toMeasure
        (sourcePairSuperpositionEvent G P) =
      ENNReal.ofReal
        (boundarySourceGatedPairSum G beta J interior internalSources
          exactSecondSources P /
          (boundarySourceCurrentSum G beta J interior internalSources *
            currentSum G beta J exactSecondSources)) := by
  rw [PMF.toMeasure_apply_eq_tsum]
  let zFirst := boundarySourceCurrentSum G beta J interior internalSources
  let zSecond := currentSum G beta J exactSecondSources
  let z : ℝ≥0∞ := (ENNReal.ofReal zFirst * ENNReal.ofReal zSecond)⁻¹
  have hpoint : ∀ pq : EdgeCurrent G × EdgeCurrent G,
      (sourcePairSuperpositionEvent G P).indicator
          (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
            internalSources exactSecondSources hfirst hsecond) pq =
        ENNReal.ofReal (boundarySourcePairRealSummand G beta J interior
          internalSources exactSecondSources P pq) * z := by
    rintro ⟨m, n⟩
    by_cases hP : P (ofEdgeFun G (fun e => m e + n e))
    · rw [Set.indicator_of_mem]
      · rw [boundarySourceCurrentPairPMF_apply,
          boundarySourceCurrentPMF_apply, currentPMF_apply]
        unfold boundarySourceCurrentRawMass currentRawMass
        by_cases hm :
            sources G (ofEdgeFun G m) ∩ interior = internalSources <;>
          by_cases hn :
            sources G (ofEdgeFun G n) = exactSecondSources <;>
          simp [hm, hn, hP, boundarySourcePairRealSummand, z,
            ENNReal.ofReal_mul,
            Ising.acw_weight_nonneg G beta J hbeta hJ]
        all_goals dsimp only [zFirst, zSecond]
        all_goals rw [ENNReal.mul_inv
          (Or.inl (ENNReal.ofReal_pos.mpr hfirst).ne')
          (Or.inl ENNReal.ofReal_ne_top)]
        all_goals ac_rfl
      · exact hP
    · rw [Set.indicator_of_notMem]
      · simp [boundarySourcePairRealSummand, hP]
      · exact hP
  rw [tsum_congr hpoint, ENNReal.tsum_mul_right]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (boundarySourcePairRealSummand_nonneg G beta J hbeta hJ interior
      internalSources exactSecondSources P)
    (summable_boundarySourcePairRealSummand G beta J interior
      internalSources exactSecondSources P)]
  have hsum :
      (∑' n : EdgeCurrent G × EdgeCurrent G,
        boundarySourcePairRealSummand G beta J interior internalSources
          exactSecondSources P n) =
        boundarySourceGatedPairSum G beta J interior internalSources
          exactSecondSources P := by
    simpa only [boundarySourcePairRealSummand] using
      (boundarySourceGatedPairSum_eq_tsum G beta J interior
        internalSources exactSecondSources P).symm
  rw [hsum]
  rw [ENNReal.ofReal_div_of_pos (mul_pos hfirst hsecond),
    ENNReal.ofReal_mul hfirst.le]
  dsimp only [zFirst, zSecond, z]
  rw [ENNReal.div_eq_inv_mul]
  ac_rfl




theorem boundarySourceCurrentPairPMF_switching
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior : Finset V) {u v : V} (huv : u ≠ v)
    (hu : u ∈ interior) (hv : v ∈ interior)
    (P : Current V → Prop) [DecidablePred P]
    (hBoundaryPair : 0 < boundarySourceCurrentSum
      G beta J interior {u, v})
    (hPair : 0 < currentSum G beta J {u, v})
    (hBoundaryZero : 0 < boundarySourceCurrentSum
      G beta J interior ∅)
    (hZero : 0 < currentSum G beta J ∅) :
    ENNReal.ofReal
        (boundarySourceCurrentSum G beta J interior {u, v} *
          currentSum G beta J {u, v}) *
      (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
        {u, v} {u, v} hBoundaryPair hPair).toMeasure
          (sourcePairSuperpositionEvent G P) =
    ENNReal.ofReal
        (boundarySourceCurrentSum G beta J interior ∅ *
          currentSum G beta J ∅) *
      (boundarySourceCurrentPairPMF G beta J hbeta hJ interior
        ∅ ∅ hBoundaryZero hZero).toMeasure
          (sourcePairSuperpositionEvent G
            (fun m => P m ∧ CurrentConnected G m u v)) := by
  rw [boundarySourceCurrentPairPMF_superpositionEvent,
    boundarySourceCurrentPairPMF_superpositionEvent]
  rw [← ENNReal.ofReal_mul (mul_pos hBoundaryPair hPair).le,
    ← ENNReal.ofReal_mul (mul_pos hBoundaryZero hZero).le]
  rw [mul_div_cancel₀ _ (mul_pos hBoundaryPair hPair).ne',
    mul_div_cancel₀ _ (mul_pos hBoundaryZero hZero).ne']
  exact congrArg ENNReal.ofReal
    (boundarySourceGatedPairSum_switching
      G beta J interior huv hu hv P)

end StatMech.FrontierB
