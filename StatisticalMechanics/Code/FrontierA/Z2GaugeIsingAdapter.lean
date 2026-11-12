/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.Z2GaugeDualCoupling
import Code.Ising.KramersWannierDuality
import Code.Sharpness.Simon

open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

noncomputable local instance gaugeIsingPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p


noncomputable def gaugeClosedSurfaceFamily (incidence : P → Finset E) :
    Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence)


noncomputable def gaugeWilsonSurfaceFamily (incidence : P → Finset E)
    (L : Finset E) : Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter
    (fun A => HasWilsonBoundary incidence A L)



noncomputable def shiftedDualCutFamily {G : SimpleGraph V}
    [DecidableRel G.Adj] (D : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  (cutSpace G).image (fun delta => delta ∆ D)



def dualPlaquetteEmbedding {G : SimpleGraph V} [DecidableRel G.Adj]
    (dualEdge : P ≃ G.edgeFinset) : P ↪ Sym2 V where
  toFun p := (dualEdge p).1
  inj' := fun _ _ h => dualEdge.injective (Subtype.ext h)



noncomputable def dualIsingCoupling {G : SimpleGraph V} [DecidableRel G.Adj]
    (dualEdge : P ≃ G.edgeFinset) (K : P → ℝ) (e : Sym2 V) : ℝ :=
  if he : e ∈ G.edgeFinset then gaugeDualCoupling (K (dualEdge.symm ⟨e, he⟩)) else 0

@[simp] theorem dualIsingCoupling_dualEdge {G : SimpleGraph V}
    [DecidableRel G.Adj] (dualEdge : P ≃ G.edgeFinset) (K : P → ℝ) (p : P) :
    dualIsingCoupling dualEdge K (dualEdge p).1 = gaugeDualCoupling (K p) := by
  rw [dualIsingCoupling, dif_pos (dualEdge p).2]
  simp



theorem sum_coupling_bond_eq_sub_cut {G : SimpleGraph V} [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, J e * bond s e) =
      (∑ e ∈ G.edgeFinset, J e) - 2 * ∑ e ∈ cutEdges G s, J e := by
  calc
    (∑ e ∈ G.edgeFinset, J e * bond s e) =
        ∑ e ∈ G.edgeFinset,
          (J e - if e ∈ cutEdges G s then 2 * J e else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcut : e ∈ cutEdges G s
      · have hb : bond s e = -1 := (Finset.mem_filter.mp hcut).2
        simp [hcut, hb]
        ring
      · have hb : bond s e = 1 := by
          rcases bond_eq_one_or_neg_one s e with hb | hb
          · exact hb
          · exact False.elim (hcut (Finset.mem_filter.mpr ⟨he, hb⟩))
        simp [hcut, hb]
    _ = (∑ e ∈ G.edgeFinset, J e) -
        ∑ e ∈ G.edgeFinset, if e ∈ cutEdges G s then 2 * J e else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ e ∈ G.edgeFinset, J e) - 2 * ∑ e ∈ cutEdges G s, J e := by
      apply congrArg (fun z => (∑ e ∈ G.edgeFinset, J e) - z)
      calc
        (∑ e ∈ G.edgeFinset,
            if e ∈ cutEdges G s then 2 * J e else 0) =
            ∑ e ∈ G.edgeFinset, if bond s e = -1 then 2 * J e else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          simp [cutEdges, he]
        _ = ∑ e ∈ cutEdges G s, 2 * J e := by
          rw [cutEdges, Finset.sum_filter]
        _ = 2 * ∑ e ∈ cutEdges G s, J e := by
          rw [Finset.mul_sum]



theorem wJ_eq_domainWallActivity {G : SimpleGraph V} [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (s : ConfigSpace V) :
    wJ G.edgeFinset J (fun _ => 0) s =
      Real.exp (∑ e ∈ G.edgeFinset, J e) *
        ∏ e ∈ cutEdges G s, Real.exp (-2 * J e) := by
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [sum_coupling_bond_eq_sub_cut]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  rw [← Finset.mul_sum]
  ring



theorem ZJ_eq_domainWallSum {G : SimpleGraph V} [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) :
    ZJ G.edgeFinset J (fun _ => 0) =
      Real.exp (∑ e ∈ G.edgeFinset, J e) *
        ∑ s : ConfigSpace V,
          ∏ e ∈ cutEdges G s, Real.exp (-2 * J e) := by
  unfold ZJ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact wJ_eq_domainWallActivity J s



theorem weightedCutSum_eq_two_mul_cutSpace {G : SimpleGraph V}
    [DecidableRel G.Adj] [Nonempty V] (hG : G.Preconnected)
    (w : Sym2 V → ℝ) :
    (∑ s : ConfigSpace V, ∏ e ∈ cutEdges G s, w e) =
      2 * ∑ delta ∈ cutSpace G, ∏ e ∈ delta, w e := by
  have hmaps : ∀ s ∈ (Finset.univ : Finset (ConfigSpace V)),
      cutEdges G s ∈ cutSpace G := by
    intro s _
    rw [cutSpace, Finset.mem_image]
    exact ⟨s, Finset.mem_univ s, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps
    (fun delta => ∏ e ∈ delta, w e)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro delta hdelta
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ.filter
        (fun s : ConfigSpace V => cutEdges G s = delta)).card : ℝ) = 2 := by
    rw [cutSpace, Finset.mem_image] at hdelta
    obtain ⟨s, _, hs⟩ := hdelta
    exact_mod_cast fiber_card_eq_two G hG hs
  rw [hcard]



theorem gaugeClosedSurfaceSum_eq_dualCutSum
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (dualEdge : P ≃ G.edgeFinset)
    (surfaceEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
    (hmap : ∀ A,
      (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    gaugeClosedSurfaceSum incidence K =
      ∑ delta ∈ cutSpace G,
        ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e) := by
  rw [gaugeClosedSurfaceSum_eq_dualActivity incidence K hK]
  change (∑ A ∈ gaugeClosedSurfaceFamily incidence,
      ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) = _
  rw [Finset.sum_subtype (p := fun A : Finset P =>
      A ∈ gaugeClosedSurfaceFamily incidence)
    (gaugeClosedSurfaceFamily incidence) (fun A => by simp)]
  rw [Finset.sum_subtype (p := fun delta : Finset (Sym2 V) =>
      delta ∈ cutSpace G) (cutSpace G) (fun delta => by simp)]
  apply Fintype.sum_equiv surfaceEquiv
  intro A
  rw [hmap A, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro p hp
  change Real.exp (-2 * gaugeDualCoupling (K p)) =
    Real.exp (-2 * dualIsingCoupling dualEdge K (dualEdge p).1)
  rw [dualIsingCoupling_dualEdge]



theorem gaugeWilsonSurfaceSum_eq_shiftedDualCutSum
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) (D : Finset (Sym2 V))
    (dualEdge : P ≃ G.edgeFinset)
    (surfaceEquiv :
      {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
        {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily (G := G) D})
    (hmap : ∀ A,
      (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    gaugeWilsonSurfaceSum incidence K L =
      ∑ gamma ∈ shiftedDualCutFamily (G := G) D,
        ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e) := by
  rw [gaugeWilsonSurfaceSum_eq_dualActivity incidence K hK L]
  change (∑ A ∈ gaugeWilsonSurfaceFamily incidence L,
      ∏ p ∈ A, Real.exp (-2 * gaugeDualCoupling (K p))) = _
  rw [Finset.sum_subtype (p := fun A : Finset P =>
      A ∈ gaugeWilsonSurfaceFamily incidence L)
    (gaugeWilsonSurfaceFamily incidence L) (fun A => by simp)]
  rw [Finset.sum_subtype (p := fun gamma : Finset (Sym2 V) =>
      gamma ∈ shiftedDualCutFamily (G := G) D)
    (shiftedDualCutFamily (G := G) D) (fun gamma => by simp)]
  apply Fintype.sum_equiv surfaceEquiv
  intro A
  rw [hmap A, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro p hp
  change Real.exp (-2 * gaugeDualCoupling (K p)) =
    Real.exp (-2 * dualIsingCoupling dualEdge K (dualEdge p).1)
  rw [dualIsingCoupling_dualEdge]



theorem gaugeWilsonExpectation_eq_dualDisorderRatio
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) (D : Finset (Sym2 V))
    (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
    (wilsonEquiv :
      {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
        {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily (G := G) D})
    (hwilson : ∀ A,
      (wilsonEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    gaugeWilsonExpectation incidence K L =
      (∑ gamma ∈ shiftedDualCutFamily (G := G) D,
          ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) /
        (∑ delta ∈ cutSpace G,
          ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
  rw [gaugeWilsonExpectation_eq_surfaceRatio]
  rw [gaugeWilsonSurfaceSum_eq_shiftedDualCutSum
    incidence K hK L D dualEdge wilsonEquiv hwilson]
  rw [gaugeClosedSurfaceSum_eq_dualCutSum
    incidence K hK dualEdge closedEquiv hclosed]





theorem gaugePartition_isingDuality
    {G : SimpleGraph V} [DecidableRel G.Adj] [Nonempty V]
    (hG : G.Preconnected) (incidence : P → Finset E)
    (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (dualEdge : P ≃ G.edgeFinset)
    (surfaceEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ cutSpace G})
    (hmap : ∀ A,
      (surfaceEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    (Real.exp (∑ e ∈ G.edgeFinset, dualIsingCoupling dualEdge K e) * 2) *
        gaugePartition incidence K =
      ((2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) *
        ZJ G.edgeFinset (dualIsingCoupling dualEdge K) (fun _ => 0) := by
  have hsurface := gaugeClosedSurfaceSum_eq_dualCutSum
    incidence K hK dualEdge surfaceEquiv hmap
  have hcuts := weightedCutSum_eq_two_mul_cutSpace hG
    (fun e => Real.exp (-2 * dualIsingCoupling dualEdge K e))
  have hZ := ZJ_eq_domainWallSum (G := G) (dualIsingCoupling dualEdge K)
  have hpart : gaugePartition incidence K =
      ((2 : ℝ) ^ Fintype.card E * ∏ p : P, Real.cosh (K p)) *
        gaugeClosedSurfaceSum incidence K := by
    simpa [gaugeClosedSurfaceSum] using gaugePartition_highTemp incidence K
  rw [hpart, hsurface, hZ, hcuts]
  ring

end StatMech.FrontierA
