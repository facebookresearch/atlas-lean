/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexAllWidthBoundaryWinding

namespace StatMech.Universality

open Complex HexWalk Set
open scoped BigOperators

noncomputable section





noncomputable def endpointMirrorBoundaryPair_of_reflection
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (heading : V → Fin 3 → ℤ)
    (hobs : ∀ z, D.obs z =
      endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
    (eNeg ePos : HexIncidence V)
    (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m →
      R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos =
      -hexPhase_sideTilt headNeg) :
    HexMirrorBoundaryPair D heading where
  neg := {eNeg}
  pos := {ePos}
  disjoint := by simp [hne]
  headNeg := headNeg
  headPos := headPos
  hHeadNeg := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadNeg
  hHeadPos := by
    intro e he
    simpa only [Finset.mem_singleton.mp he] using hHeadPos
  angle := hexPhase_sideTilt headNeg + (5 / 8 : ℝ) * W
  mass := endpointCountObservable R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi
  phaseNeg := by
    rw [Finset.sum_singleton, hobs,
      endpointParafObservable_factor R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) (5 / 8) hexChi W hdetNeg]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  phasePos := by
    have hdetPos := endpoint_det_winding_reflect R.inRegion R.start h0
      (D.mid eNeg.vtx eNeg.edge) W hsym hdetNeg
    rw [Finset.sum_singleton, hobs, hmidPos,
      endpointParafObservable_factor R.inRegion R.start h0
        (hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
        (5 / 8) hexChi (-W) hdetPos,
      endpointCountObservable_refl R.inRegion R.start h0
        (D.mid eNeg.vtx eNeg.edge) hexChi hsym]
    rw [← mul_assoc, ← Complex.exp_add, htilt]
    congr 2
    push_cast
    ring


theorem endpointMirrorBoundaryPair_mass_nonneg
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (heading : V → Fin 3 → ℤ)
    (hobs : ∀ z, D.obs z =
      endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
    (eNeg ePos : HexIncidence V) (hne : eNeg ≠ ePos)
    (headNeg headPos : ℤ)
    (hHeadNeg : heading eNeg.vtx eNeg.edge = headNeg)
    (hHeadPos : heading ePos.vtx ePos.edge = headPos)
    (hmidPos : D.mid ePos.vtx ePos.edge =
      hsc_refl R.start h0 (D.mid eNeg.vtx eNeg.edge))
    (hsym : ∀ m, R.inRegion m → R.inRegion (hsc_refl R.start h0 m))
    (W : ℝ)
    (hdetNeg : ∀ ts,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt
            (D.mid eNeg.vtx eNeg.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (htilt : hexPhase_sideTilt headPos = -hexPhase_sideTilt headNeg) :
    0 ≤ (endpointMirrorBoundaryPair_of_reflection heading hobs eNeg ePos
      hne headNeg headPos hHeadNeg hHeadPos hmidPos hsym W hdetNeg htilt).mass := by
  change 0 ≤ endpointCountObservable R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi
  unfold endpointCountObservable
  exact tsum_nonneg (endpointCountWeight_nonneg R.inRegion R.start h0
    (D.mid eNeg.vtx eNeg.edge) hexChi_pos.le)


noncomputable def endpointFixedBoundaryPoint_of_winding
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    (heading : V → Fin 3 → ℤ)
    (hobs : ∀ z, D.obs z =
      endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi)
    (e : HexIncidence V) (head : ℤ)
    (hHead : heading e.vtx e.edge = head)
    (W : ℝ)
    (hdet : ∀ ts,
      (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt (D.mid e.vtx e.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (hphase : hexPhase_sideTilt head = -(5 / 8 : ℝ) * W) :
    HexFixedBoundaryPoint D heading where
  incidence := e
  head := head
  hHead := hHead
  mass := endpointCountObservable R.inRegion R.start h0
    (D.mid e.vtx e.edge) hexChi
  mass_nonneg := by
    unfold endpointCountObservable
    exact tsum_nonneg (endpointCountWeight_nonneg R.inRegion R.start h0
      (D.mid e.vtx e.edge) hexChi_pos.le)
  phase := by
    rw [hobs,
      endpointParafObservable_factor R.inRegion R.start h0
        (D.mid e.vtx e.edge) (5 / 8) hexChi W hdet]
    congr 2
    rw [hphase]
    push_cast
    ring






structure HexEndpointBoundaryCore
    {V : Type*} [DecidableEq V]
    (R : HexFiniteRegion) (h0 : ℤ) (D : HexDomain V)
    (P : D.InteriorPairing) where
  interior_sub : P.interior ⊆ D.incidences
  obs_eq : ∀ z, D.obs z =
    endpointParafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  start_value : D.obs R.start = 1



structure HexEndpointMirrorOrbitData
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexEndpointBoundaryCore R h0 D P) where
  heading : V → Fin 3 → ℤ
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  startIncidence : HexIncidence V
  start_mid : D.mid startIncidence.vtx startIncidence.edge = R.start
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  pairs : I → HexMirrorBoundaryPair D heading
  fixed : K → HexFixedBoundaryPoint D heading
  boundary_partition :
    D.incidences \ P.interior =
      {startIncidence} ∪ Finset.univ.biUnion (fun o : I ⊕ K =>
        match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece)
  start_orbits_disjoint :
    Disjoint ({startIncidence} : Finset (HexIncidence V))
      (Finset.univ.biUnion (fun o : I ⊕ K =>
        match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece))
  orbits_disjoint :
    ((Finset.univ : Finset (I ⊕ K)) : Set (I ⊕ K)).PairwiseDisjoint
      (fun o => match o with
        | .inl i => (pairs i).piece
        | .inr k => (fixed k).piece)

namespace HexEndpointMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]
variable [DecidableEq I] [DecidableEq K] [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexEndpointBoundaryCore R h0 D P}

variable (H : HexEndpointMirrorOrbitData (I := I) (K := K) C)


noncomputable def totalContribution : ℝ :=
  (∑ i : I, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) +
    ∑ k : K, (H.fixed k).mass

private theorem pair_incTerm_sum (i : I) :
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
  calc
    (∑ e ∈ (H.pairs i).piece, D.incTerm e) =
        ∑ e ∈ (H.pairs i).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.pairs i).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) := by
      rw [(H.pairs i).unit_projection]
      ring

private theorem fixed_incTerm_sum (k : K) :
    (∑ e ∈ (H.fixed k).piece, D.incTerm e) =
      (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
  calc
    (∑ e ∈ (H.fixed k).piece, D.incTerm e) =
        ∑ e ∈ (H.fixed k).piece,
          ((1 / 2 : ℂ) * hexUnit (H.heading e.vtx e.edge)) *
            D.obs (D.mid e.vtx e.edge) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [HexDomain.incTerm, H.hgeom]
    _ = (1 / 2 : ℂ) *
        (∑ e ∈ (H.fixed k).piece,
          hexUnit (H.heading e.vtx e.edge) *
            D.obs (D.mid e.vtx e.edge)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
      rw [(H.fixed k).unit_projection]
      ring

private theorem start_incTerm :
    D.incTerm H.startIncidence = -(1 / 2 : ℂ) * Complex.I := by
  rw [HexDomain.incTerm, H.hgeom, H.start_heading, H.start_mid,
    C.start_value, hexStart_hexUnit_four]
  ring


theorem boundarySum_eq :
    D.boundarySum P =
      (1 / 2 : ℂ) * Complex.I * ((H.totalContribution - 1 : ℝ) : ℂ) := by
  unfold HexDomain.boundarySum
  rw [H.boundary_partition,
    Finset.sum_union H.start_orbits_disjoint,
    Finset.sum_singleton,
    Finset.sum_biUnion H.orbits_disjoint,
    H.start_incTerm]
  calc
    -(1 / 2 : ℂ) * Complex.I +
          ∑ o : I ⊕ K, ∑ e ∈ match o with
            | .inl i => (H.pairs i).piece
            | .inr k => (H.fixed k).piece, D.incTerm e =
        -(1 / 2 : ℂ) * Complex.I +
          (∑ i : I, (1 / 2 : ℂ) * Complex.I *
              ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ)) +
          ∑ k : K, (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
      rw [Fintype.sum_sum_type]
      simp only
      rw [show (∑ i : I, ∑ e ∈ (H.pairs i).piece, D.incTerm e) =
          ∑ i : I, (1 / 2 : ℂ) * Complex.I *
            ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ) by
        apply Finset.sum_congr rfl
        intro i _
        exact H.pair_incTerm_sum i,
        show (∑ k : K, ∑ e ∈ (H.fixed k).piece, D.incTerm e) =
          ∑ k : K, (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) by
        apply Finset.sum_congr rfl
        intro k _
        exact H.fixed_incTerm_sum k]
      ring
    _ = (1 / 2 : ℂ) * Complex.I *
        ((H.totalContribution - 1 : ℝ) : ℂ) := by
      unfold totalContribution
      push_cast
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring


theorem totalContribution_eq_one : H.totalContribution = 1 := by
  have hraw := D.hexBoundaryRaw P C.interior_sub
  rw [H.boundarySum_eq] at hraw
  have hfac : (1 / 2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hz : (((H.totalContribution - 1 : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp hraw).resolve_left hfac
  have hzReal : H.totalContribution - 1 = 0 := by
    exact_mod_cast hz
  linarith



structure DCSClassification where
  classOf : I → HexPairedBoundaryClass
  cos_angle : ∀ i,
    Real.cos (H.pairs i).angle =
      match classOf i with
      | .side => hexCl
      | .slant => hexCt
      | .top => 1

variable (Kc : DCSClassification H)

noncomputable def pairClassMass (k : HexPairedBoundaryClass) : ℝ :=
  ∑ i : I, if Kc.classOf i = k then 2 * (H.pairs i).mass else 0

noncomputable def fixedMass : ℝ := ∑ k : K, (H.fixed k).mass


noncomputable def dcsLam : ℝ := H.pairClassMass Kc .side
noncomputable def dcsTau : ℝ := H.pairClassMass Kc .slant
noncomputable def dcsUps : ℝ := H.pairClassMass Kc .top + H.fixedMass

theorem pairClassMass_nonneg
    (hpairs : ∀ i, 0 ≤ (H.pairs i).mass)
    (k : HexPairedBoundaryClass) :
    0 ≤ H.pairClassMass Kc k := by
  classical
  unfold pairClassMass
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (by norm_num) (hpairs i)
  · exact le_rfl

theorem fixedMass_nonneg : 0 ≤ H.fixedMass := by
  unfold fixedMass
  exact Finset.sum_nonneg (fun k _ => (H.fixed k).mass_nonneg)

theorem dcs_values_nonneg
    (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
    0 ≤ H.dcsLam Kc ∧ 0 ≤ H.dcsTau Kc ∧ 0 ≤ H.dcsUps Kc := by
  exact ⟨H.pairClassMass_nonneg Kc hpairs .side,
    H.pairClassMass_nonneg Kc hpairs .slant,
    add_nonneg (H.pairClassMass_nonneg Kc hpairs .top)
      H.fixedMass_nonneg⟩

private theorem pair_term_decompose (i : I) :
    2 * Real.cos (H.pairs i).angle * (H.pairs i).mass =
      hexCl * (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
      hexCt * (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
      (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) := by
  rw [Kc.cos_angle i]
  cases hclass : Kc.classOf i <;> simp [hclass] <;> ring

theorem totalContribution_decompose :
    H.totalContribution =
      hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc := by
  classical
  unfold totalContribution dcsLam dcsTau dcsUps pairClassMass fixedMass
  calc
    (∑ i : I, 2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) +
        ∑ k : K, (H.fixed k).mass =
      (∑ i : I,
        (hexCl * (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
          hexCt * (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
          (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0))) +
        ∑ k : K, (H.fixed k).mass := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact H.pair_term_decompose Kc i
    _ = hexCl * (∑ i : I,
          if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
        hexCt * (∑ i : I,
          if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
        ((∑ i : I,
          if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) +
          ∑ k : K, (H.fixed k).mass) := by
      simp only [Finset.sum_add_distrib]
      repeat rw [← Finset.mul_sum]
      ring


theorem normalized_dcs_identity :
    hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
  rw [← H.totalContribution_decompose Kc]
  exact H.totalContribution_eq_one

end HexEndpointMirrorOrbitData

end


end StatMech.Universality
