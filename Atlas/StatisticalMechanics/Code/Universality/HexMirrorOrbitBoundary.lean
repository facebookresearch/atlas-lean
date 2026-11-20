/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















import Code.Universality.HexMirrorPairFromReflection

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators






structure HexFixedBoundaryPoint
    {V : Type*} [DecidableEq V]
    (D : HexDomain V) (heading : V → Fin 3 → ℤ) where
  incidence : HexIncidence V
  head : ℤ
  hHead : heading incidence.vtx incidence.edge = head
  mass : ℝ
  mass_nonneg : 0 ≤ mass
  phase : D.obs (D.mid incidence.vtx incidence.edge) =
    Complex.exp ((hexPhase_sideTilt head : ℝ) * Complex.I) * (mass : ℂ)

namespace HexFixedBoundaryPoint

variable {V : Type*} [DecidableEq V]
variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


noncomputable def piece (Q : HexFixedBoundaryPoint D heading) :
    Finset (HexIncidence V) := {Q.incidence}


theorem unit_projection (Q : HexFixedBoundaryPoint D heading) :
    (∑ e ∈ Q.piece,
      hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
        Complex.I * (Q.mass : ℂ) := by
  rw [piece, Finset.sum_singleton, Q.hHead]
  exact hexUnitPhase_proj_complex Q.head (Q.mass : ℂ)
    (D.obs (D.mid Q.incidence.vtx Q.incidence.edge)) Q.phase

end HexFixedBoundaryPoint




noncomputable def hexFixedBoundaryPoint_of_winding
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P)
    (heading : V → Fin 3 → ℤ)
    (e : HexIncidence V) (head : ℤ)
    (hHead : heading e.vtx e.edge = head)
    (W : ℝ)
    (hdet : ∀ ts,
      (ofTurns R.start h0 ts).IsLegalSAW ∧
          (ofTurns R.start h0 ts).StaysIn R.inRegion ∧
          (ofTurns R.start h0 ts).EndsAt (D.mid e.vtx e.edge) →
        (ofTurns R.start h0 ts).turning = W)
    (hphase : hexPhase_sideTilt head = -(5 / 8 : ℝ) * W) :
    HexFixedBoundaryPoint D heading where
  incidence := e
  head := head
  hHead := hHead
  mass := hexClosed_countObs R.inRegion R.start h0
    (D.mid e.vtx e.edge) hexChi
  mass_nonneg := tsum_nonneg (fun ts =>
    hexClosed_cw_nonneg R.inRegion R.start h0
      (D.mid e.vtx e.edge) hexChi_pos.le ts)
  phase := by
    rw [C.obs_eq,
      hexClosed_parafObservable_factor R.inRegion R.start h0
        (D.mid e.vtx e.edge) (5 / 8) hexChi W hdet]
    congr 2
    rw [hphase]
    push_cast
    ring





structure HexFiniteStripMirrorOrbitData
    {I K V : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (C : HexFiniteStripBoundaryCore R h0 D P) where
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
      {startIncidence} ∪
        Finset.univ.biUnion (fun o : I ⊕ K =>
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

namespace HexFiniteStripMirrorOrbitData

variable {I K V : Type*} [Fintype I] [Fintype K]
variable [DecidableEq I] [DecidableEq K] [DecidableEq V]
variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
variable {P : D.InteriorPairing}
variable {C : HexFiniteStripBoundaryCore R h0 D P}

variable (H : HexFiniteStripMirrorOrbitData (I := I) (K := K) C)


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
    D.incTerm H.startIncidence =
      -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) := by
  rw [HexDomain.incTerm, H.hgeom, H.start_heading, H.start_mid, ← C.Fa_eq,
    hexStart_hexUnit_four]
  ring

private theorem orbit_incTerm_sum (o : I ⊕ K) :
    (∑ e ∈ match o with
        | .inl i => (H.pairs i).piece
        | .inr k => (H.fixed k).piece,
      D.incTerm e) =
      match o with
      | .inl i => (1 / 2 : ℂ) * Complex.I *
          ((2 * Real.cos (H.pairs i).angle * (H.pairs i).mass : ℝ) : ℂ)
      | .inr k => (1 / 2 : ℂ) * Complex.I * ((H.fixed k).mass : ℂ) := by
  cases o with
  | inl i => exact H.pair_incTerm_sum i
  | inr k => exact H.fixed_incTerm_sum k



theorem boundarySum_eq :
    D.boundarySum P =
      (1 / 2 : ℂ) * Complex.I *
        ((H.totalContribution - C.Fa : ℝ) : ℂ) := by
  unfold HexDomain.boundarySum
  rw [H.boundary_partition,
    Finset.sum_union H.start_orbits_disjoint,
    Finset.sum_singleton,
    Finset.sum_biUnion H.orbits_disjoint,
    H.start_incTerm]
  calc
    -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
          ∑ o : I ⊕ K, ∑ e ∈ match o with
            | .inl i => (H.pairs i).piece
            | .inr k => (H.fixed k).piece, D.incTerm e =
        -(1 / 2 : ℂ) * Complex.I * (C.Fa : ℂ) +
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
        ((H.totalContribution - C.Fa : ℝ) : ℂ) := by
      unfold totalContribution
      push_cast
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring



theorem totalContribution_eq_Fa : H.totalContribution = C.Fa := by
  have hraw := D.hexBoundaryRaw P C.interior_sub
  rw [H.boundarySum_eq] at hraw
  have hfac : (1 / 2 : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hz : (((H.totalContribution - C.Fa : ℝ) : ℂ)) = 0 :=
    (mul_eq_zero.mp hraw).resolve_left hfac
  have hzReal : H.totalContribution - C.Fa = 0 := by
    exact_mod_cast hz
  linarith


theorem normalized_totalContribution :
    hexChi⁻¹ * H.totalContribution = 1 := by
  rw [H.totalContribution_eq_Fa, C.Fa_eq_hexChi]
  exact inv_mul_cancel₀ (ne_of_gt hexChi_pos)





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

noncomputable def dcsLam : ℝ := hexChi⁻¹ * H.pairClassMass Kc .side
noncomputable def dcsTau : ℝ := hexChi⁻¹ * H.pairClassMass Kc .slant
noncomputable def dcsUps : ℝ :=
  hexChi⁻¹ * (H.pairClassMass Kc .top + H.fixedMass)

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




theorem normalized_class_values_nonneg
    (hpairs : ∀ i, 0 ≤ (H.pairs i).mass) :
    0 ≤ H.dcsLam Kc ∧ 0 ≤ H.dcsTau Kc ∧ 0 ≤ H.dcsUps Kc := by
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (H.pairClassMass_nonneg Kc hpairs .side)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (H.pairClassMass_nonneg Kc hpairs .slant)
  · exact mul_nonneg (inv_nonneg.mpr hexChi_pos.le)
      (add_nonneg (H.pairClassMass_nonneg Kc hpairs .top)
        H.fixedMass_nonneg)

private theorem pair_term_decompose (i : I) :
    hexChi⁻¹ * (2 * Real.cos (H.pairs i).angle * (H.pairs i).mass) =
      hexCl * (hexChi⁻¹ *
        (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0)) +
      hexCt * (hexChi⁻¹ *
        (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0)) +
      hexChi⁻¹ *
        (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) := by
  rw [Kc.cos_angle i]
  cases hclass : Kc.classOf i <;> simp <;> ring



theorem normalized_totalContribution_decompose :
    hexChi⁻¹ * H.totalContribution =
      hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc := by
  classical
  unfold totalContribution dcsLam dcsTau dcsUps pairClassMass fixedMass
  rw [mul_add, Finset.mul_sum]
  calc
    (∑ i : I, hexChi⁻¹ *
        (2 * Real.cos (H.pairs i).angle * (H.pairs i).mass)) +
        hexChi⁻¹ * ∑ k : K, (H.fixed k).mass =
      (∑ i : I,
        (hexCl * (hexChi⁻¹ *
            (if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0)) +
          hexCt * (hexChi⁻¹ *
            (if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0)) +
          hexChi⁻¹ *
            (if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0))) +
        hexChi⁻¹ * ∑ k : K, (H.fixed k).mass := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact H.pair_term_decompose Kc i
    _ = hexCl * (hexChi⁻¹ * ∑ i : I,
          if Kc.classOf i = .side then 2 * (H.pairs i).mass else 0) +
        hexCt * (hexChi⁻¹ * ∑ i : I,
          if Kc.classOf i = .slant then 2 * (H.pairs i).mass else 0) +
        hexChi⁻¹ * ((∑ i : I,
          if Kc.classOf i = .top then 2 * (H.pairs i).mass else 0) +
          ∑ k : K, (H.fixed k).mass) := by
      simp only [Finset.sum_add_distrib]
      repeat rw [← Finset.mul_sum]
      ring


theorem normalized_dcs_identity :
    hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
  rw [← H.normalized_totalContribution_decompose Kc]
  exact H.normalized_totalContribution

end HexFiniteStripMirrorOrbitData

end StatMech.Universality
