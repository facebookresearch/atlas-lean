/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierB.FiniteNormalizedSwitching
import Code.FrontierB.FiniteBoundaryCurrentLaw
import Code.FrontierB.FiniteCurrentPairLaw

open scoped symmDiff

namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance boundarySwitchingPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p


def sourceToggleEquiv (U : Finset V) : Finset V ≃ Finset V where
  toFun A := A ∆ U
  invFun A := A ∆ U
  left_inv A := symmDiff_symmDiff_cancel_right U A
  right_inv A := symmDiff_symmDiff_cancel_right U A



theorem sourceToggle_inter_eq_iff
    (interior U A : Finset V) (hU : U ⊆ interior) :
    (A ∆ U) ∩ interior = U ↔ A ∩ interior = ∅ := by
  constructor
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    have hxU : x ∈ U → x ∈ interior := fun hxU => hU hxU
    simp only [Finset.mem_inter, Finset.mem_symmDiff,
      Finset.notMem_empty] at hx ⊢
    tauto
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    have hxU : x ∈ U → x ∈ interior := fun hxU => hU hxU
    simp only [Finset.mem_inter, Finset.mem_symmDiff,
      Finset.notMem_empty] at hx ⊢
    tauto



noncomputable def boundarySourceSectorSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) : ℝ :=
  ∑ A : Finset V,
    if A ∩ interior = internalSources then currentSum G beta J A else 0




noncomputable def boundarySourceCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) : ℝ :=
  ∑' m : EdgeCurrent G,
    if sources G (ofEdgeFun G m) ∩ interior = internalSources then
      weight G beta J (ofEdgeFun G m)
    else 0



noncomputable def boundarySourceGatedPairSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P] : ℝ :=
  ∑ A : Finset V,
    if A ∩ interior = internalSources then
      gatedSourcePairSum G beta J A exactSecondSources P
    else 0



theorem boundarySourceGatedPairSum_eq_tsum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources exactSecondSources : Finset V)
    (P : Current V → Prop) [DecidablePred P] :
    boundarySourceGatedPairSum G beta J interior internalSources
        exactSecondSources P =
      ∑' pq : EdgeCurrent G × EdgeCurrent G,
        (if sources G (ofEdgeFun G pq.1) ∩ interior = internalSources then
          weight G beta J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = exactSecondSources then
          weight G beta J (ofEdgeFun G pq.2) else 0) *
        (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0) := by
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
  rw [boundarySourceGatedPairSum]
  calc
    (∑ A : Finset V,
        if A ∩ interior = internalSources then
          gatedSourcePairSum G beta J A exactSecondSources P
        else 0) = ∑ A : Finset V, ∑' pq, f A pq := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A ∩ interior = internalSources
      · simp only [hA, if_true, f, gatedSourcePairSum]
      · simp only [hA, if_false, f, tsum_zero]
    _ = ∑' pq, ∑ A : Finset V, f A pq := by
      symm
      exact Summable.tsum_finsetSum (s := Finset.univ)
        (fun A _ => hf A)
    _ = _ := by
      apply tsum_congr
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
        simp [f, hfirst, hsecond, hP]



theorem boundarySourceCurrentSum_eq_boundarySourceSectorSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (interior internalSources : Finset V) :
    boundarySourceCurrentSum G beta J interior internalSources =
      boundarySourceSectorSum G beta J interior internalSources := by
  unfold boundarySourceCurrentSum boundarySourceSectorSum currentSum
  let f : Finset V → EdgeCurrent G → ℝ := fun A m =>
    if A ∩ interior = internalSources then
      if sources G (ofEdgeFun G m) = A then
        weight G beta J (ofEdgeFun G m)
      else 0
    else 0
  have hf : ∀ A : Finset V, Summable (f A) := by
    intro A
    by_cases hA : A ∩ interior = internalSources
    · simpa only [f, hA, if_true] using
        (summable_norm_currentSum_summand G beta J A).of_norm
    · simp only [f, hA, if_false]
      exact summable_zero
  calc
    (∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) ∩ interior = internalSources then
          weight G beta J (ofEdgeFun G m) else 0) =
        ∑' m : EdgeCurrent G, ∑ A : Finset V, f A m := by
      apply tsum_congr
      intro m
      rw [show (∑ A : Finset V, f A m) =
          f (sources G (ofEdgeFun G m)) m by
        rw [Finset.sum_eq_single (sources G (ofEdgeFun G m))]
        · intro A _ hA
          by_cases hsector : A ∩ interior = internalSources
          · simp [f, hsector, Ne.symm hA]
          · simp [f, hsector]
        · intro hmem
          exact (hmem (Finset.mem_univ _)).elim]
      simp [f]
    _ = ∑ A : Finset V, ∑' m : EdgeCurrent G, f A m :=
      Summable.tsum_finsetSum (s := Finset.univ)
        (fun A _ => hf A)
    _ = ∑ A : Finset V,
        if A ∩ interior = internalSources then
          ∑' m : EdgeCurrent G,
            if sources G (ofEdgeFun G m) = A then
              weight G beta J (ofEdgeFun G m)
            else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A ∩ interior = internalSources
      · simp only [f, hA, if_true]
      · simp only [f, hA, if_false, tsum_zero]
    _ = _ := rfl



theorem boundaryCurrentSum_eq_boundarySourceCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryCurrentSum G beta J interior =
      boundarySourceCurrentSum G beta J interior ∅ := rfl



theorem boundaryCurrentSum_eq_boundarySourceSectorSum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryCurrentSum G beta J interior =
      boundarySourceSectorSum G beta J interior ∅ := by
  rw [boundaryCurrentSum_eq_boundarySourceCurrentSum,
    boundarySourceCurrentSum_eq_boundarySourceSectorSum]



theorem currentSum_le_boundarySourceCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources A : Finset V)
    (hA : A ∩ interior = internalSources) :
    currentSum G beta J A ≤
      boundarySourceCurrentSum G beta J interior internalSources := by
  rw [boundarySourceCurrentSum_eq_boundarySourceSectorSum]
  unfold boundarySourceSectorSum
  have hnonneg : ∀ B : Finset V,
      0 ≤ if B ∩ interior = internalSources then currentSum G beta J B else 0 := by
    intro B
    split
    · exact Ising.acr_currentSum_nonneg G beta J hbeta hJ B
    · exact le_rfl
  simpa [hA] using
    (Finset.single_le_sum (fun B _ => hnonneg B) (Finset.mem_univ A))



theorem boundarySourceCurrentSum_pos_of_currentSum_pos
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (interior internalSources A : Finset V)
    (hA : A ∩ interior = internalSources)
    (hpos : 0 < currentSum G beta J A) :
    0 < boundarySourceCurrentSum G beta J interior internalSources :=
  lt_of_lt_of_le hpos
    (currentSum_le_boundarySourceCurrentSum G beta J hbeta hJ
      interior internalSources A hA)






theorem boundarySourceGatedPairSum_switching
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V)
    {u v : V} (huv : u ≠ v)
    (hu : u ∈ interior) (hv : v ∈ interior)
    (P : Current V → Prop) [DecidablePred P] :
    boundarySourceGatedPairSum G beta J interior {u, v} {u, v} P =
      boundarySourceGatedPairSum G beta J interior ∅ ∅
        (fun m => P m ∧ CurrentConnected G m u v) := by
  let U : Finset V := {u, v}
  have hU : U ⊆ interior := by
    intro x hx
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  unfold boundarySourceGatedPairSum
  change (∑ A : Finset V,
      if A ∩ interior = U then gatedSourcePairSum G beta J A U P else 0) = _
  calc
    (∑ A : Finset V,
        if A ∩ interior = U then gatedSourcePairSum G beta J A U P else 0) =
        ∑ A : Finset V,
          if (A ∆ U) ∩ interior = U then
            gatedSourcePairSum G beta J (A ∆ U) U P
          else 0 := by
      symm
      exact (sourceToggleEquiv U).sum_comp
        (fun A : Finset V =>
          if A ∩ interior = U then
            gatedSourcePairSum G beta J A U P
          else 0)
    _ = ∑ A : Finset V,
        if A ∩ interior = ∅ then
          gatedSourcePairSum G beta J A ∅
            (fun m => P m ∧ CurrentConnected G m u v)
        else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [if_congr (sourceToggle_inter_eq_iff interior U A hU) rfl rfl]
      by_cases hA : A ∩ interior = ∅
      · simp only [hA, if_true]
        simpa only [U] using gatedSourcePairSum_switching G beta J A huv P
      · simp only [hA, if_false]
    _ = _ := rfl

end StatMech.FrontierB
