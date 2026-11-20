/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.Universality.HexFiniteStripNormalizedBoundary
import Code.Universality.HexBoundaryPhases

namespace StatMech.Universality

open Complex HexWalk Set




theorem hexContourSum_empty
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexContourSum inRegion a h0 ∅ x = 0 := by
  unfold hexContourSum
  letI : IsEmpty {ts // ts ∈ hexContourFamily inRegion a h0 (∅ : Set ℂ)} :=
    ⟨fun ts => by
      rcases ts.property.2.2 with ⟨z, hz, _⟩
      exact hz.elim⟩
  exact tsum_empty



theorem hexContourFamily_singleton_start
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ)
    (hreg : inRegion a) :
    hexContourFamily inRegion a h0 ({a} : Set ℂ) = {[]} := by
  ext ts
  constructor
  · rintro ⟨hlegal, hstay, z, hz, hend⟩
    have hza : z = a := by simpa using hz
    subst z
    exact hexReturningLegalSAW_eq_nil a h0 ts hlegal hend
  · intro hts
    have hnil : ts = [] := by simpa using hts
    subst ts
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, a, by simp,
      trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      change (trivialWalk a h0).mids = [a]
      unfold HexWalk.mids trivialWalk
      simp [midsAux]
    rw [hmids] at hm
    exact (List.mem_singleton.mp hm) ▸ hreg



theorem hexContourSum_singleton_start
    (inRegion : ℂ → Prop) (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hreg : inRegion a) :
    hexContourSum inRegion a h0 ({a} : Set ℂ) x = x := by
  rw [hexContourSum, hexContourFamily_singleton_start inRegion a h0 hreg]
  let w0 : {ts : List ℤ // ts ∈ ({[]} : Set (List ℤ))} := ⟨[], by simp⟩
  rw [tsum_eq_single w0]
  · simp [w0, ofTurns]
  · intro w hw
    exfalso
    apply hw
    apply Subtype.ext
    change w.val = w0.val
    have hprop := w.property
    change w.val = [] at hprop
    exact hprop





noncomputable def hexEmptyIncidenceDomain
    (R : HexFiniteRegion) (h0 : ℤ) : HexDomain (Fin 0) where
  interiorVertices := ∅
  pos := fun v => Fin.elim0 v
  mid := fun v => Fin.elim0 v
  obs := fun z => parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  relation := by
    intro v
    exact Fin.elim0 v


@[simp] theorem hexEmptyIncidenceDomain_incidences
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).incidences = ∅ := by
  simp [HexDomain.incidences, hexEmptyIncidenceDomain]


def hexEmptyIncidencePairing
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).InteriorPairing where
  interior := ∅
  pair := id
  pair_mem := by simp
  pair_invol := by simp
  pair_ne := by simp
  cancel := by simp



def hexEmptyIncidenceSides (R : HexFiniteRegion) : HexContourSides where
  bottom := ∅
  slantPlus := ∅
  slantMinus := ∅
  top := {R.start}










noncomputable def hexEmptyIncidenceBoundaryData
    (R : HexFiniteRegion) (h0 : ℤ) :
    HexFiniteStripBoundaryData R h0
      (hexEmptyIncidenceDomain R h0) (hexEmptyIncidencePairing R h0) where
  sides := hexEmptyIncidenceSides R
  interior_sub := by simp [hexEmptyIncidencePairing]
  vertex_mem := by
    intro v
    exact Fin.elim0 v
  mid_mem := by
    intro e he
    simp at he
  obs_eq := by
    intro z
    rfl
  lam := 0
  tau := 0
  ups := hexChi
  Fa := hexChi
  lam_eq := by
    simp [hexContourLambda, hexEmptyIncidenceSides, hexContourSum_empty]
  tau_eq := by
    simp [hexContourTauPlus, hexContourTauMinus, hexEmptyIncidenceSides,
      hexContourSum_empty]
  ups_eq := by
    simp only [hexContourUpsilon, hexEmptyIncidenceSides]
    exact (hexContourSum_singleton_start R.inRegion R.start h0 hexChi
      (by simpa [HexFiniteRegion.inRegion] using R.start_mem)).symm
  Fa_eq := by
    change (hexChi : ℂ) = parafObservable R.inRegion R.start h0 R.start
      (5 / 8) hexChi
    symm
    exact parafObservable_start_eq_weight R.inRegion R.start h0
      (5 / 8) hexChi (by simpa [HexFiniteRegion.inRegion] using R.start_mem)
  alphaRest := 0
  alphaRest_eq := by simp
  betaSum := hexChi
  betaSum_eq := rfl
  epsSum := 0
  epsSum_eq := by simp
  epsbarSum := 0
  epsbarSum_eq := by simp
  contour_eq := by
    simp [HexDomain.boundarySum, hexEmptyIncidencePairing,
      hexFiniteStripRaw]



theorem hexEmptyIncidenceBoundaryData_no_incidences
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).incidences = ∅ :=
  hexEmptyIncidenceDomain_incidences R h0



theorem hexEmptyIncidenceBoundaryData_topContour_eq
    (R : HexFiniteRegion) (h0 : ℤ) :
    hexContourUpsilon R.inRegion R.start h0
      (hexEmptyIncidenceBoundaryData R h0).sides hexChi = hexChi :=
  (hexEmptyIncidenceBoundaryData R h0).ups_eq.symm

theorem hexEmptyIncidenceBoundaryData_topContour_ne_zero
    (R : HexFiniteRegion) (h0 : ℤ) :
    hexContourUpsilon R.inRegion R.start h0
      (hexEmptyIncidenceBoundaryData R h0).sides hexChi ≠ 0 := by
  rw [hexEmptyIncidenceBoundaryData_topContour_eq]
  exact ne_of_gt hexChi_pos





def hexFiniteStripContourPart
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P) (k : Fin 5) (z : ℂ) : Prop :=
  (k = 0 ∧ z = R.start)
    ∨ (k = 1 ∧ z ∈ B.sides.bottom)
    ∨ (k = 2 ∧ z ∈ B.sides.slantPlus)
    ∨ (k = 3 ∧ z ∈ B.sides.slantMinus)
    ∨ (k = 4 ∧ z ∈ B.sides.top)











structure HexFiniteStripIncidenceEnumeration
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing}
    (B : HexFiniteStripBoundaryData R h0 D P) where
  
  mid_complete : ∀ m ∈ R.mids, ∃ e ∈ D.incidences,
    D.mid e.vtx e.edge = m
  
  boundary_mid_injective : ∀ e₁ ∈ D.incidences \ P.interior,
    ∀ e₂ ∈ D.incidences \ P.interior,
      D.mid e₁.vtx e₁.edge = D.mid e₂.vtx e₂.edge → e₁ = e₂
  

  boundary_classified : ∀ e ∈ D.incidences \ P.interior,
    D.mid e.vtx e.edge = R.start
      ∨ D.mid e.vtx e.edge ∈ B.sides.bottom
      ∨ D.mid e.vtx e.edge ∈ B.sides.slantPlus
      ∨ D.mid e.vtx e.edge ∈ B.sides.slantMinus
      ∨ D.mid e.vtx e.edge ∈ B.sides.top
  
  part_unique : ∀ z ∈ R.mids, ∀ k l : Fin 5,
    hexFiniteStripContourPart B k z →
      hexFiniteStripContourPart B l z → k = l
  

  side_complete : ∀ z ∈ R.mids,
    (z = R.start ∨ z ∈ B.sides.bottom ∨ z ∈ B.sides.slantPlus
      ∨ z ∈ B.sides.slantMinus ∨ z ∈ B.sides.top) →
    ∃ e ∈ D.incidences \ P.interior, D.mid e.vtx e.edge = z




theorem hexEmptyIncidenceBoundaryData_not_enumerated
    (R : HexFiniteRegion) (h0 : ℤ) :
    ¬ Nonempty (HexFiniteStripIncidenceEnumeration
      (hexEmptyIncidenceBoundaryData R h0)) := by
  rintro ⟨E⟩
  obtain ⟨e, he, _⟩ := E.mid_complete R.start R.start_mem
  rw [hexEmptyIncidenceDomain_incidences] at he
  simp at he






theorem HexPhaseData.startFiber_nonempty_of_Fa_ne_zero
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (hFa : H.Fa ≠ 0) :
    ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).Nonempty := by
  by_contra hempty
  have hfiber : (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hphase := H.phaseA
  rw [hfiber] at hphase
  simp only [Finset.sum_empty] at hphase
  have hreal : (-1 : ℝ) * H.Fa ≠ 0 := mul_ne_zero (by norm_num) hFa
  have hrhs : 2 * Complex.exp
        ((hexPhase_sideTilt H.headA : ℝ) * Complex.I)
      * (((-1 : ℝ) * H.Fa : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr hreal)
  exact hrhs hphase.symm










theorem HexPhaseData.Fa_eq_zero_of_startFiber_singleton
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (eA : HexIncidence V)
    (hfiber :
      (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {eA})
    (hmid : D.mid eA.vtx eA.edge = G.start)
    (hobs : D.obs G.start = (H.Fa : ℂ)) :
    H.Fa = 0 := by
  have hphase := H.phaseA
  rw [hfiber, Finset.sum_singleton, hmid, hobs] at hphase
  have hnorm := congrArg norm hphase
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_eq_abs, norm_neg, abs_one, one_mul,
    mul_one] at hnorm
  have habs : |H.Fa| = 0 := by
    nlinarith [abs_nonneg H.Fa]
  exact abs_eq_zero.mp habs



theorem HexPhaseData.not_startFiber_singleton_of_Fa_eq_hexChi
    {V : Type*} [DecidableEq V]
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (H : HexPhaseData D P G) (eA : HexIncidence V)
    (hfiber :
      (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {eA})
    (hmid : D.mid eA.vtx eA.edge = G.start)
    (hobs : D.obs G.start = (H.Fa : ℂ))
    (hFa : H.Fa = hexChi) : False := by
  have hzero := H.Fa_eq_zero_of_startFiber_singleton eA hfiber hmid hobs
  rw [hFa] at hzero
  exact (ne_of_gt hexChi_pos) hzero










theorem HexFiniteStripBoundaryData.phaseA_startFiber_card_ne_one
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (H : HexPhaseData D P G)
    (hstart : G.start = R.start)
    (hFa : H.Fa = B.Fa)
    (hmid : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0),
      D.mid e.vtx e.edge = G.start) :
    ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card ≠ 1 := by
  intro hcard
  obtain ⟨eA, hfiber⟩ := Finset.card_eq_one.mp hcard
  have heA : eA ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) := by
    rw [hfiber]
    simp
  have hobs : D.obs G.start = (H.Fa : ℂ) := by
    calc
      D.obs G.start = D.obs R.start := by rw [hstart]
      _ = (B.Fa : ℂ) := B.Fa_eq.symm
      _ = (H.Fa : ℂ) := by rw [hFa]
  exact H.not_startFiber_singleton_of_Fa_eq_hexChi eA hfiber
    (hmid eA heA) hobs (hFa.trans B.Fa_eq_hexChi)




theorem HexFiniteStripBoundaryData.two_le_phaseA_startFiber_card
    {V : Type*} [DecidableEq V]
    {R : HexFiniteRegion} {h0 : ℤ}
    {D : HexDomain V} {P : D.InteriorPairing} {G : HexRegion}
    (B : HexFiniteStripBoundaryData R h0 D P)
    (H : HexPhaseData D P G)
    (hstart : G.start = R.start)
    (hFa : H.Fa = B.Fa)
    (hmid : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0),
      D.mid e.vtx e.edge = G.start) :
    2 ≤ ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card := by
  have hFa0 : H.Fa ≠ 0 := by
    rw [hFa, B.Fa_eq_hexChi]
    exact ne_of_gt hexChi_pos
  have hpos : 0 < ((D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0)).card :=
    Finset.card_pos.mpr (H.startFiber_nonempty_of_Fa_ne_zero hFa0)
  have hone := B.phaseA_startFiber_card_ne_one H hstart hFa hmid
  omega

end StatMech.Universality
