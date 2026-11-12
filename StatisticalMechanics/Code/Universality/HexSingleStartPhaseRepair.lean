/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























import Code.Universality.HexProjPhaseClose
import Code.Universality.HexFiniteStripNormalizedBoundary

namespace StatMech.Universality

open Complex
open scoped BigOperators

variable {V : Type*} [DecidableEq V]












structure HexSingleStartPhaseData
    (D : HexDomain V) (P : D.InteriorPairing) (R : HexRegion) where
  
  heading : V → Fin 3 → ℤ
  
  hgeom : ∀ v j,
    D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  
  startInc : HexIncidence V
  
  startFiber :
    (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0) = {startInc}
  
  startMid : D.mid startInc.vtx startInc.edge = R.start
  
  startHeading : heading startInc.vtx startInc.edge = 4
  
  headL : ℤ
  
  headTp : ℤ
  
  headTm : ℤ
  
  headU : ℤ
  
  hHeadL : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 1),
    heading e.vtx e.edge = headL
  
  hHeadTp : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 2),
    heading e.vtx e.edge = headTp
  
  hHeadTm : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 3),
    heading e.vtx e.edge = headTm
  
  hHeadU : ∀ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 4),
    heading e.vtx e.edge = headU
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  obsStart : D.obs R.start = (Fa : ℂ)
  
  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 1),
      D.obs (D.mid e.vtx e.edge))
    = 2 * Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I)
      * ((hexBdryCl * lam : ℝ) : ℂ)
  
  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 2),
      D.obs (D.mid e.vtx e.edge))
    = 2 * Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I)
      * ((hexBdryCt * taup : ℝ) : ℂ)
  
  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 3),
      D.obs (D.mid e.vtx e.edge))
    = 2 * Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I)
      * ((hexBdryCt * taum : ℝ) : ℂ)
  
  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 4),
      D.obs (D.mid e.vtx e.edge))
    = 2 * Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I)
      * ((ups : ℝ) : ℂ)

namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)

include H in

@[simp] theorem startFiber_card :
    ((D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)).card = 1 := by
  rw [H.startFiber]
  simp


theorem eq_startInc_of_mem_startFiber
    (e : HexIncidence V)
    (he : e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)) :
    e = H.startInc := by
  rw [H.startFiber] at he
  exact Finset.mem_singleton.mp he


theorem heading_eq_four_on_startFiber
    (e : HexIncidence V)
    (he : e ∈ (D.incidences \ P.interior).filter
      (fun e ↦ hexRegionClsInc R D e = 0)) :
    H.heading e.vtx e.edge = 4 := by
  have heq := H.eq_startInc_of_mem_startFiber e he
  subst e
  exact H.startHeading





theorem startProjection :
    ((1 / 2 : ℂ) * hexUnit 4) *
        (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e ↦ hexRegionClsInc R D e = 0),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * (H.Fa / 2) : ℝ) : ℂ) := by
  rw [H.startFiber, Finset.sum_singleton, H.startMid, H.obsStart,
    hpp_alphaDir]
  push_cast
  ring



theorem startProjection_hexChi (hFa : H.Fa = hexChi) :
    ((1 / 2 : ℂ) * hexUnit 4) *
        (∑ e ∈ (D.incidences \ P.interior).filter
          (fun e ↦ hexRegionClsInc R D e = 0),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * (hexChi / 2) : ℝ) : ℂ) := by
  simpa [hFa] using H.startProjection








noncomputable def toHalfStartRegionAssign : HexRegionAssign D P R where
  heading := H.heading
  hgeom := H.hgeom
  headA := 4
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.heading_eq_four_on_startFiber
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := H.lam
  taup := H.taup
  taum := H.taum
  ups := H.ups
  Fa := H.Fa / 2
  projA := H.startProjection
  projL := hexPhase_projL H.headL H.lam H.phaseL
  projTp := hexPhase_projTp H.headTp H.taup H.phaseTp
  projTm := hexPhase_projTm H.headTm H.taum H.phaseTm
  projU := hexPhase_projU H.headU H.ups H.phaseU

@[simp] theorem toHalfStartRegionAssign_lam :
    H.toHalfStartRegionAssign.lam = H.lam := rfl

@[simp] theorem toHalfStartRegionAssign_taup :
    H.toHalfStartRegionAssign.taup = H.taup := rfl

@[simp] theorem toHalfStartRegionAssign_taum :
    H.toHalfStartRegionAssign.taum = H.taum := rfl

@[simp] theorem toHalfStartRegionAssign_ups :
    H.toHalfStartRegionAssign.ups = H.ups := rfl

@[simp] theorem toHalfStartRegionAssign_Fa :
    H.toHalfStartRegionAssign.Fa = H.Fa / 2 := rfl

end HexSingleStartPhaseData






theorem hexBdryAssign_identity_fa
    {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
    (hsub : P.interior ⊆ D.incidences)
    (A : HexRegionAssign D P R) :
    hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = A.Fa := by
  have hraw := D.hexBoundaryRaw P hsub
  have hdecomp := A.toDecomp.boundarySum_eq
  rw [hraw] at hdecomp
  have hcast' :
      ((hexBdryCl * A.toDecomp.lam
          + hexBdryCt * (A.toDecomp.taup + A.toDecomp.taum)
          + A.toDecomp.ups : ℝ) : ℂ) - (A.toDecomp.Fa : ℂ) = 0 := by
    exact (mul_eq_zero.mp hdecomp.symm).resolve_left Complex.I_ne_zero
  have hcast :
      ((hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups : ℝ) : ℂ)
          - (A.Fa : ℂ) = 0 := by
    simpa only [HexRegionAssign.toDecomp, HexRegionAssign.toFamilyData,
      HexFamilyData.toDecomp] using hcast'
  have hreal :
      (hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups : ℝ)
          - A.Fa = 0 := by
    exact_mod_cast hcast
  linarith

namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)





theorem correctedInterface_identity_half
    (hsub : P.interior ⊆ D.incidences) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = H.Fa / 2 := by
  have h := hexBdryAssign_identity_fa hsub H.toHalfStartRegionAssign
  exact h



theorem correctedInterface_identity_hexChi_half
    (hsub : P.interior ⊆ D.incidences) (hFa : H.Fa = hexChi) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
      = hexChi / 2 := by
  calc
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
        = H.Fa / 2 := H.correctedInterface_identity_half hsub
    _ = hexChi / 2 := by rw [hFa]




theorem correctedInterface_normalized_identity
    (hsub : P.interior ⊆ D.incidences) (hFa : H.Fa = hexChi) :
    hexBdryCl * ((2 * hexChi⁻¹) * H.lam)
      + hexBdryCt * ((2 * hexChi⁻¹) * (H.taup + H.taum))
      + (2 * hexChi⁻¹) * H.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := H.correctedInterface_identity_hexChi_half hsub hFa
  calc
    hexBdryCl * ((2 * hexChi⁻¹) * H.lam)
          + hexBdryCt * ((2 * hexChi⁻¹) * (H.taup + H.taum))
          + (2 * hexChi⁻¹) * H.ups
        = (2 * hexChi⁻¹) *
            (hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups) := by
              ring
    _ = (2 * hexChi⁻¹) * (hexChi / 2) := by rw [h]
    _ = 1 := by field_simp





theorem Fa_eq_boundaryData_Fa
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) : H.Fa = B.Fa := by
  apply Complex.ofReal_injective
  calc
    (H.Fa : ℂ) = D.obs R.start := H.obsStart.symm
    _ = D.obs Rf.start := by rw [hstart]
    _ = (B.Fa : ℂ) := B.Fa_eq.symm



theorem Fa_eq_hexChi_of_boundaryData
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) : H.Fa = hexChi :=
  (H.Fa_eq_boundaryData_Fa B hstart).trans B.Fa_eq_hexChi





theorem diagnostic_half_identity_of_boundaryData
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
      = hexChi / 2 :=
  H.correctedInterface_identity_hexChi_half B.interior_sub
    (H.Fa_eq_hexChi_of_boundaryData B hstart)








theorem boundaryData_identity_of_halfScaled_contours
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start)
    (hlam : H.lam = B.lam / 2)
    (htau : H.taup + H.taum = B.tau / 2)
    (hups : H.ups = B.ups / 2) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = hexChi := by
  have h := H.diagnostic_half_identity_of_boundaryData B hstart
  rw [hlam, htau, hups] at h
  linarith



theorem normalized_boundaryData_identity_of_halfScaled_contours
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start)
    (hlam : H.lam = B.lam / 2)
    (htau : H.taup + H.taum = B.tau / 2)
    (hups : H.ups = B.ups / 2) :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := H.boundaryData_identity_of_halfScaled_contours
    B hstart hlam htau hups
  calc
    hexBdryCl * (hexChi⁻¹ * B.lam)
          + hexBdryCt * (hexChi⁻¹ * B.tau)
          + hexChi⁻¹ * B.ups
        = hexChi⁻¹ *
            (hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [h]
    _ = 1 := inv_mul_cancel₀ hchi

end HexSingleStartPhaseData

namespace HexFiniteStripBoundaryData



theorem obs_start_eq_hexChi
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P) :
    D.obs R.start = (hexChi : ℂ) := by
  calc
    D.obs R.start = (B.Fa : ℂ) := B.Fa_eq.symm
    _ = (hexChi : ℂ) := by rw [B.Fa_eq_hexChi]

end HexFiniteStripBoundaryData

end StatMech.Universality
