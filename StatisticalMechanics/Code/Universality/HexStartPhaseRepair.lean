/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























import Code.Universality.HexFiniteStripIncidenceObstruction

namespace StatMech.Universality

open Complex HexWalk
open scoped BigOperators

variable {V : Type*} [DecidableEq V]




noncomputable def hexFiniteStripPhysicalStartFiber
    {R : HexFiniteRegion} {D : HexDomain V} (P : D.InteriorPairing) :
    Finset (HexIncidence V) :=
  (D.incidences \ P.interior).filter
    (fun e => D.mid e.vtx e.edge = R.start)


theorem HexFiniteStripIncidenceEnumeration.exists_startIncidence
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    ∃ eA : HexIncidence V,
      hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
  obtain ⟨eA, heA, hmidA⟩ :=
    E.side_complete R.start R.start_mem (Or.inl rfl)
  refine ⟨eA, ?_⟩
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter,
    Finset.mem_singleton]
  constructor
  · rintro ⟨he, hmid⟩
    exact E.boundary_mid_injective e he eA heA (hmid.trans hmidA.symm)
  · rintro rfl
    exact ⟨heA, hmidA⟩


theorem HexFiniteStripIncidenceEnumeration.startFiber_card_eq_one
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) :
    (hexFiniteStripPhysicalStartFiber (R := R) P).card = 1 := by
  obtain ⟨eA, heA⟩ := E.exists_startIncidence
  rw [heA, Finset.card_singleton]



theorem HexFiniteStripIncidenceEnumeration.exists_classifiedStartIncidence
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) (G : HexRegion)
    (hclass : ∀ e ∈ D.incidences \ P.interior,
      hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
    ∃ eA : HexIncidence V,
      (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0) = {eA} := by
  obtain ⟨eA, heA⟩ := E.exists_startIncidence
  refine ⟨eA, ?_⟩
  rw [← heA]
  ext e
  simp only [hexFiniteStripPhysicalStartFiber, Finset.mem_filter]
  constructor
  · rintro ⟨he, hzero⟩
    exact ⟨he, (hclass e he).mp hzero⟩
  · rintro ⟨he, hmid⟩
    exact ⟨he, (hclass e he).mpr hmid⟩




theorem HexFiniteStripIncidenceEnumeration.exists_classifiedStartData
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} {B : HexFiniteStripBoundaryData R h0 D P}
    (E : HexFiniteStripIncidenceEnumeration B) (G : HexRegion)
    (hstart : G.start = R.start)
    (hclass : ∀ e ∈ D.incidences \ P.interior,
      hexRegionClsInc G D e = 0 ↔ D.mid e.vtx e.edge = R.start) :
    ∃ eA : HexIncidence V,
      (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0) = {eA}
        ∧ D.mid eA.vtx eA.edge = G.start := by
  obtain ⟨eA, hfiber⟩ := E.exists_classifiedStartIncidence G hclass
  have heA : eA ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 0) := by
    rw [hfiber]
    simp
  have heBoundary : eA ∈ D.incidences \ P.interior :=
    (Finset.mem_filter.mp heA).1
  have hzero : hexRegionClsInc G D eA = 0 :=
    (Finset.mem_filter.mp heA).2
  refine ⟨eA, hfiber, ?_⟩
  exact ((hclass eA heBoundary).mp hzero).trans hstart.symm




theorem hexStart_hexUnit_four : hexUnit (4 : ℤ) = -Complex.I := by
  rw [hexPhase_hexUnit_normalForm]
  have htilt : hexPhase_sideTilt (4 : ℤ) = -Real.pi := by
    unfold hexPhase_sideTilt
    norm_num
    ring
  rw [htilt]
  simp



theorem hexUnitPhase_proj (h : ℤ) (cmag : ℝ) (fSum : ℂ)
    (hphase : fSum =
      Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) :
    hexUnit h * fSum = Complex.I * (cmag : ℂ) := by
  have hdouble : 2 * fSum =
      2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ) := by
    rw [hphase]
    ring
  have hp := hexPhase_proj h cmag (2 * fSum) hdouble
  calc
    hexUnit h * fSum = ((1 / 2 : ℂ) * hexUnit h) * (2 * fSum) := by ring
    _ = Complex.I * (cmag : ℂ) := hp



theorem hexUnitPhase_half_proj (h : ℤ) (coeff value : ℝ) (fSum : ℂ)
    (hphase : fSum =
      Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I)
        * ((coeff * value : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit h) * fSum =
      Complex.I * ((coeff * (value / 2) : ℝ) : ℂ) := by
  have hp := hexUnitPhase_proj h (coeff * value) fSum hphase
  calc
    ((1 / 2 : ℂ) * hexUnit h) * fSum =
        (1 / 2 : ℂ) * (hexUnit h * fSum) := by ring
    _ = (1 / 2 : ℂ) * (Complex.I * ((coeff * value : ℝ) : ℂ)) := by rw [hp]
    _ = Complex.I * ((coeff * (value / 2) : ℝ) : ℂ) := by
      push_cast
      ring






structure HexFiniteStripBoundaryCore
    (R : HexFiniteRegion) (h0 : ℤ) (D : HexDomain V)
    (P : D.InteriorPairing) where
  sides : HexContourSides
  interior_sub : P.interior ⊆ D.incidences
  vertex_mem : ∀ v ∈ D.interiorVertices, D.pos v ∈ R.verts
  mid_mem : ∀ e ∈ D.incidences, D.mid e.vtx e.edge ∈ R.mids
  obs_eq : ∀ z, D.obs z =
    parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  lam : ℝ
  tau : ℝ
  ups : ℝ
  Fa : ℝ
  lam_eq : lam =
    hexContourLambda R.inRegion R.start h0 sides hexChi
  tau_eq : tau =
    hexContourTauPlus R.inRegion R.start h0 sides hexChi
      + hexContourTauMinus R.inRegion R.start h0 sides hexChi
  ups_eq : ups =
    hexContourUpsilon R.inRegion R.start h0 sides hexChi
  Fa_eq : (Fa : ℂ) = D.obs R.start

namespace HexFiniteStripBoundaryCore

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing}


def ofBoundaryData (B : HexFiniteStripBoundaryData R h0 D P) :
    HexFiniteStripBoundaryCore R h0 D P where
  sides := B.sides
  interior_sub := B.interior_sub
  vertex_mem := B.vertex_mem
  mid_mem := B.mid_mem
  obs_eq := B.obs_eq
  lam := B.lam
  tau := B.tau
  ups := B.ups
  Fa := B.Fa
  lam_eq := B.lam_eq
  tau_eq := B.tau_eq
  ups_eq := B.ups_eq
  Fa_eq := B.Fa_eq


theorem Fa_eq_hexChi (C : HexFiniteStripBoundaryCore R h0 D P) :
    C.Fa = hexChi := by
  apply Complex.ofReal_injective
  calc
    (C.Fa : ℂ) = D.obs R.start := C.Fa_eq
    _ = parafObservable R.inRegion R.start h0 R.start (5 / 8) hexChi :=
      C.obs_eq R.start
    _ = (hexChi : ℂ) :=
      parafObservable_start_eq_weight_of_unique
        R.inRegion R.start h0 (5 / 8) hexChi
        (by simpa [HexFiniteRegion.inRegion] using R.start_mem)
        (by
          intro ts hts
          exact hexReturningLegalSAW_eq_nil R.start h0 ts hts.1 hts.2.2)

@[simp] theorem ofBoundaryData_Fa
    (B : HexFiniteStripBoundaryData R h0 D P) :
    (ofBoundaryData B).Fa = B.Fa := rfl

end HexFiniteStripBoundaryCore










structure HexFiniteStripFourPhaseData
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} (C : HexFiniteStripBoundaryCore R h0 D P)
    (G : HexRegion) where
  
  start_eq : G.start = R.start
  
  heading : V → Fin 3 → ℤ
  
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  
  startIncidence : HexIncidence V
  
  startFiber_singleton :
    (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0) = {startIncidence}
  
  start_mid : D.mid startIncidence.vtx startIncidence.edge = G.start
  
  start_heading : heading startIncidence.vtx startIncidence.edge = 4
  
  headL : ℤ
  headTp : ℤ
  headTm : ℤ
  headU : ℤ
  hHeadL : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 1),
    heading e.vtx e.edge = headL
  hHeadTp : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 2),
    heading e.vtx e.edge = headTp
  hHeadTm : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 3),
    heading e.vtx e.edge = headTm
  hHeadU : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e => hexRegionClsInc G D e = 4),
    heading e.vtx e.edge = headU
  
  taup : ℝ
  taum : ℝ
  tau_eq : taup + taum = C.tau
  
  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 1),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I)
      * ((hexBdryCl * C.lam : ℝ) : ℂ)
  
  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 2),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I)
      * ((hexBdryCt * taup : ℝ) : ℂ)
  
  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 3),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I)
      * ((hexBdryCt * taum : ℝ) : ℂ)
  
  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 4),
      D.obs (D.mid e.vtx e.edge)) =
    Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I)
      * ((C.ups : ℝ) : ℂ)

namespace HexFiniteStripFourPhaseData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
  {G : HexRegion} (H : HexFiniteStripFourPhaseData C G)

include H


theorem startFSum_eq_Fa :
    (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0),
      D.obs (D.mid e.vtx e.edge)) = (C.Fa : ℂ) := by
  rw [H.startFiber_singleton, Finset.sum_singleton, H.start_mid, H.start_eq]
  exact C.Fa_eq.symm


theorem startFSum_eq_hexChi :
    (∑ e ∈ (D.incidences \ P.interior).filter
        (fun e => hexRegionClsInc G D e = 0),
      D.obs (D.mid e.vtx e.edge)) = (hexChi : ℂ) := by
  rw [H.startFSum_eq_Fa, C.Fa_eq_hexChi]



theorem normalized_startFSum_eq_one :
    (hexChi : ℂ)⁻¹ *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) = 1 := by
  rw [H.startFSum_eq_hexChi]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos))



theorem projA_unit :
    hexUnit 4 *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) =
      Complex.I * (((-1 : ℝ) * C.Fa : ℝ) : ℂ) := by
  rw [H.startFSum_eq_Fa, hexStart_hexUnit_four]
  push_cast
  ring



theorem normalized_startContribution_eq_neg_one :
    -(hexChi : ℂ)⁻¹ *
      (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e => hexRegionClsInc G D e = 0),
        D.obs (D.mid e.vtx e.edge)) = -1 := by
  rw [H.startFSum_eq_hexChi]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos)]



theorem hHeadA : ∀ e ∈ (D.incidences \ P.interior).filter
    (fun e => hexRegionClsInc G D e = 0),
    H.heading e.vtx e.edge = 4 := by
  intro e he
  have he' : e ∈ ({H.startIncidence} : Finset (HexIncidence V)) := by
    rw [← H.startFiber_singleton]
    exact he
  have heq : e = H.startIncidence := by simpa using he'
  subst e
  exact H.start_heading




noncomputable def toHalfRegionAssign : HexRegionAssign D P G where
  heading := H.heading
  hgeom := H.hgeom
  headA := 4
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.hHeadA
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := C.lam / 2
  taup := H.taup / 2
  taum := H.taum / 2
  ups := C.ups / 2
  Fa := C.Fa / 2
  projA := by
    have hp := H.projA_unit
    calc
      ((1 / 2 : ℂ) * hexUnit 4) *
            (∑ e ∈ (D.incidences \ P.interior).filter
                (fun e => hexRegionClsInc G D e = 0),
              D.obs (D.mid e.vtx e.edge)) =
          (1 / 2 : ℂ) *
            (hexUnit 4 *
              (∑ e ∈ (D.incidences \ P.interior).filter
                  (fun e => hexRegionClsInc G D e = 0),
                D.obs (D.mid e.vtx e.edge))) := by ring
      _ = (1 / 2 : ℂ) *
          (Complex.I * (((-1 : ℝ) * C.Fa : ℝ) : ℂ)) := by rw [hp]
      _ = Complex.I * (((-1 : ℝ) * (C.Fa / 2) : ℝ) : ℂ) := by
        push_cast
        ring
  projL := hexUnitPhase_half_proj H.headL hexBdryCl C.lam _ H.phaseL
  projTp := hexUnitPhase_half_proj H.headTp hexBdryCt H.taup _ H.phaseTp
  projTm := hexUnitPhase_half_proj H.headTm hexBdryCt H.taum _ H.phaseTm
  projU := by
    simpa using
      (hexUnitPhase_half_proj H.headU 1 C.ups _ (by simpa using H.phaseU))

@[simp] theorem toHalfRegionAssign_lam : H.toHalfRegionAssign.lam = C.lam / 2 := rfl
@[simp] theorem toHalfRegionAssign_taup : H.toHalfRegionAssign.taup = H.taup / 2 := rfl
@[simp] theorem toHalfRegionAssign_taum : H.toHalfRegionAssign.taum = H.taum / 2 := rfl
@[simp] theorem toHalfRegionAssign_ups : H.toHalfRegionAssign.ups = C.ups / 2 := rfl
@[simp] theorem toHalfRegionAssign_Fa : H.toHalfRegionAssign.Fa = C.Fa / 2 := rfl



theorem boundary_identity_fa :
    hexBdryCl * C.lam + hexBdryCt * (H.taup + H.taum) + C.ups = C.Fa := by
  have hraw : D.boundarySum P = 0 := D.hexBoundaryRaw P C.interior_sub
  have hdecomp := H.toHalfRegionAssign.toDecomp.boundarySum_eq
  rw [hraw] at hdecomp
  simp only [HexRegionAssign.toDecomp, HexRegionAssign.toFamilyData,
    HexFamilyData.toDecomp, toHalfRegionAssign] at hdecomp
  have hzero :
      ((hexBdryCl * (C.lam / 2)
          + hexBdryCt * (H.taup / 2 + H.taum / 2)
          + C.ups / 2 : ℝ) : ℂ) - ((C.Fa / 2 : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hdecomp.symm with hi | hz
    · exact (Complex.I_ne_zero hi).elim
    · exact hz
  have hreal :
      (hexBdryCl * (C.lam / 2)
          + hexBdryCt * (H.taup / 2 + H.taum / 2)
          + C.ups / 2 : ℝ) - C.Fa / 2 = 0 := by
    exact_mod_cast hzero
  linarith



theorem normalized_boundary_identity :
    hexBdryCl * (hexChi⁻¹ * C.lam)
      + hexBdryCt * (hexChi⁻¹ * C.tau)
      + hexChi⁻¹ * C.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have hid := H.boundary_identity_fa
  rw [H.tau_eq, C.Fa_eq_hexChi] at hid
  calc
    hexBdryCl * (hexChi⁻¹ * C.lam)
          + hexBdryCt * (hexChi⁻¹ * C.tau)
          + hexChi⁻¹ * C.ups =
        hexChi⁻¹ *
          (hexBdryCl * C.lam + hexBdryCt * C.tau + C.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [hid]
    _ = 1 := inv_mul_cancel₀ hchi



theorem normalized_contour_boundary_identity :
    hexBdryCl *
        (hexChi⁻¹ *
          hexContourLambda R.inRegion R.start h0 C.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 C.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 C.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 C.sides hexChi = 1 := by
  rw [← C.lam_eq, ← C.tau_eq, ← C.ups_eq]
  exact H.normalized_boundary_identity

end HexFiniteStripFourPhaseData

end StatMech.Universality
