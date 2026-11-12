/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SpinWeightedBase









namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

def ons_restrictEdgeWeight
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L))) :
    Sym2 (ZMod L × ZMod L) → ℂ :=
  fun edge => if edge ∈ S then weight edge else 0

theorem norm_ons_restrictEdgeWeight_le
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L))) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q) (edge) :
    ‖ons_restrictEdgeWeight weight S edge‖ ≤ q := by
  unfold ons_restrictEdgeWeight
  split
  · exact hweight edge
  · simpa using hq

theorem ons_scale_restrict_insert_one
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L)))
    (edge : Sym2 (ZMod L × ZMod L)) :
    ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 1 =
      ons_restrictEdgeWeight weight (insert edge S) := by
  funext f
  simp only [ons_scaleEdgeWeight]
  split <;> ring

theorem ons_scale_restrict_insert_zero
    {L : ℕ} (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (S : Finset (Sym2 (ZMod L × ZMod L)))
    (edge : Sym2 (ZMod L × ZMod L)) (hedge : edge ∉ S) :
    ons_scaleEdgeWeight (ons_restrictEdgeWeight weight (insert edge S)) edge 0 =
      ons_restrictEdgeWeight weight S := by
  funext f
  unfold ons_scaleEdgeWeight ons_restrictEdgeWeight
  by_cases hfe : f = edge
  · subst f
    simp [hedge]
  · simp [hfe]

theorem ons_KWmatWeightedPhase_restrict_edgeFinset
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega u v : ℂ) :
    ons_KWmatWeightedPhase L
        (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) omega u v =
      ons_KWmatWeightedPhase L weight omega u v := by
  ext d2 d1
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted ons_restrictEdgeWeight
  rw [if_pos (ons_portEdge_mem_edgeFinset L d1)]

theorem ons_weightedSpinCharacterSum_restrict_edgeFinset
    (L : ℕ) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L
        (ons_restrictEdgeWeight weight (onsTorusGraph L).edgeFinset) a b =
      ons_weightedSpinCharacterSum L weight a b := by
  unfold ons_weightedSpinCharacterSum
  apply Finset.sum_congr rfl
  intro F hF
  apply congrArg ((ons_spinCharacter a b (ons_evenHomology L F) : ℂ) * ·)
  apply Finset.prod_congr rfl
  intro edge hedge
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  simp [ons_restrictEdgeWeight, hdata.1 hedge]



def ons_weightedEdgeCoefficientIdentity (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ (a b : Fin 2)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (q : ℝ),
    0 ≤ q →
    (∀ edge, ‖weight edge‖ ≤ q) →
    q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹ →
    ∀ e : ons_Dart L,
    ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) =
      -ons_detWalkRoot
          (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (∑' s, ons_firstReturnWeight
          (ons_KWmatWeightedPhase L weight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s)

theorem ons_weightedRootIdentity_of_edgeCoefficient
    (L : ℕ) [Fact (2 < L)]
    (hcoeff : ons_weightedEdgeCoefficientIdentity L) :
    ons_weightedRootIdentity L := by
  intro a b weight q hq hweight hsmall
  have hind : ∀ S : Finset (Sym2 (ZMod L × ZMod L)),
      S ⊆ (onsTorusGraph L).edgeFinset →
      ons_detWalkRoot
          (ons_KWmatWeightedPhase L (ons_restrictEdgeWeight weight S)
            ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) =
        ons_weightedSpinCharacterSum L (ons_restrictEdgeWeight weight S) a b := by
    intro S hsub
    induction S using Finset.induction with
    | empty =>
        simpa [ons_restrictEdgeWeight] using ons_weightedRoot_zero L a b
    | @insert edge S hedge ih =>
        have hSsub : S ⊆ (onsTorusGraph L).edgeFinset := by
          intro f hf
          exact hsub (Finset.mem_insert_of_mem hf)
        have hedgeG : edge ∈ (onsTorusGraph L).edgeFinset :=
          hsub (Finset.mem_insert_self edge S)
        obtain ⟨e, he⟩ := ons_torusEdge_eq_portEdge L hedgeG
        let wI := ons_restrictEdgeWeight weight (insert edge S)
        have hwI : ∀ f, ‖wI f‖ ≤ q :=
          norm_ons_restrictEdgeWeight_le weight _ q hq hweight
        have hzeroW :
            ons_scaleEdgeWeight wI (ons_portEdge L e) 0 =
              ons_restrictEdgeWeight weight S := by
          rw [he]
          exact ons_scale_restrict_insert_zero weight S edge hedge
        have honeW :
            ons_scaleEdgeWeight wI (ons_portEdge L e) 1 = wI := by
          rw [he]
          exact ons_scale_restrict_insert_one weight S edge
        have hstep := ons_weightedRoot_eq_spin_scaleEdge_of_coefficient
          L wI a b q hq hwI 1 (by norm_num) e hsmall
          (by simpa only [hzeroW] using ih hSsub)
          (hcoeff a b wI q hq hwI hsmall e)
        simpa only [honeW, wI] using hstep
  have hfull := hind (onsTorusGraph L).edgeFinset Finset.Subset.rfl
  rw [ons_KWmatWeightedPhase_restrict_edgeFinset,
    ons_weightedSpinCharacterSum_restrict_edgeFinset] at hfull
  exact hfull

end StatMech.Onsager
