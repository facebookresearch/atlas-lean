/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Code.Universality.HexBoundaryAssign

namespace StatMech.Universality

open Complex
open scoped BigOperators


















noncomputable def hexPhase_sideTilt (h : ℤ) : ℝ := (1 - (h : ℝ)) * (Real.pi / 3)



@[simp] theorem hexPhase_sideTilt_one : hexPhase_sideTilt 1 = 0 := by
  unfold hexPhase_sideTilt; simp






theorem hexPhase_keyfac (θ : ℝ) :
    Complex.I * Complex.exp ((-θ : ℝ) * Complex.I)
      = Complex.exp (((Real.pi / 2 - θ : ℝ) : ℂ) * Complex.I) := by
  nth_rewrite 1 [show Complex.I = Complex.exp ((↑Real.pi / 2 : ℂ) * Complex.I) from
    exp_pi_div_two_mul_I.symm]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring













theorem hexPhase_hexUnit_normalForm (h : ℤ) :
    hexUnit h = Complex.I * Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I) := by
  rw [hexPhase_keyfac]
  unfold hexUnit hexPhase_sideTilt
  congr 1
  push_cast
  ring


















theorem hexPhase_reflection_madeReal (φ r : ℝ) :
    Complex.exp ((-φ : ℝ) * Complex.I) * (r : ℂ)
        + Complex.exp ((φ : ℝ) * Complex.I) * (r : ℂ)
      = ((2 * Real.cos φ * r : ℝ) : ℂ) := by
  have h2 : Complex.exp ((φ : ℝ) * Complex.I) + Complex.exp ((-φ : ℝ) * Complex.I)
      = 2 * (Real.cos φ : ℂ) := hexExpI_add_neg φ
  have key : Complex.exp ((-φ : ℝ) * Complex.I) * (r : ℂ)
        + Complex.exp ((φ : ℝ) * Complex.I) * (r : ℂ)
      = (Complex.exp ((φ : ℝ) * Complex.I) + Complex.exp ((-φ : ℝ) * Complex.I)) * (r : ℂ) := by
    ring
  rw [key, h2]; push_cast; ring













theorem hexPhase_cl_from_turning : hexBdryCl = -Real.cos (5 * Real.pi / 8) := by
  unfold hexBdryCl
  rw [show (5 * Real.pi / 8 : ℝ) = Real.pi - 3 * Real.pi / 8 by ring, Real.cos_pi_sub]
  ring


theorem hexPhase_cl_winding_angle : (5 * Real.pi / 8 : ℝ) = (5 / 8 : ℝ) * Real.pi := by ring



theorem hexPhase_ct_eq : hexBdryCt = Real.cos (Real.pi / 4) := rfl


theorem hexPhase_cu_eq : (1 : ℝ) = Real.cos 0 := (Real.cos_zero).symm



























theorem hexPhase_proj (h : ℤ) (cmag : ℝ) (fSum : ℂ)
    (hphase : fSum = 2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit h) * fSum = Complex.I * (cmag : ℂ) := by
  rw [hphase, hexPhase_hexUnit_normalForm]
  have hexp : Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I)
        * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) = 1 := by
    rw [← Complex.exp_add,
      show ((-(hexPhase_sideTilt h) : ℝ) : ℂ) * Complex.I
          + (hexPhase_sideTilt h : ℝ) * Complex.I = 0 by push_cast; ring]
    exact Complex.exp_zero
  calc
    ((1 / 2 : ℂ) * (Complex.I * Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I)))
        * (2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ))
      = Complex.I * (cmag : ℂ)
          * (Complex.exp ((-(hexPhase_sideTilt h) : ℝ) * Complex.I)
              * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I)) := by ring
    _ = Complex.I * (cmag : ℂ) := by rw [hexp]; ring












theorem hexPhase_proj_atTilt (θ : ℝ) (c : ℂ) :
    (Complex.I * Complex.exp ((-θ : ℝ) * Complex.I))
        * (Complex.exp ((θ : ℝ) * Complex.I) * ((Real.cos θ : ℂ) * c))
      = Complex.I * ((Real.cos θ : ℂ) * c) :=
  HexSide.proj_of_tilt θ c









variable {V : Type*} [DecidableEq V]
  {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}



theorem hexPhase_projA (headA : ℤ) (Fa : ℝ)
    (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headA : ℝ) * Complex.I) * (((-1 : ℝ) * Fa : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit headA) *
        (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ) :=
  hexPhase_proj headA ((-1 : ℝ) * Fa) _ hphase





theorem hexPhase_projL (headL : ℤ) (lam : ℝ)
    (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I) * ((hexBdryCl * lam : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit headL) *
        (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ) :=
  hexPhase_proj headL (hexBdryCl * lam) _ hphase



theorem hexPhase_projTp (headTp : ℤ) (taup : ℝ)
    (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I) * ((hexBdryCt * taup : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit headTp) *
        (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ) :=
  hexPhase_proj headTp (hexBdryCt * taup) _ hphase



theorem hexPhase_projTm (headTm : ℤ) (taum : ℝ)
    (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I) * ((hexBdryCt * taum : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit headTm) *
        (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ) :=
  hexPhase_proj headTm (hexBdryCt * taum) _ hphase





theorem hexPhase_projU (headU : ℤ) (ups : ℝ)
    (hphase : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I) * ((ups : ℝ) : ℂ)) :
    ((1 / 2 : ℂ) * hexUnit headU) *
        (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
          D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((ups : ℝ) : ℂ) :=
  hexPhase_proj headU ups _ hphase






















structure HexPhaseData (D : HexDomain V) (P : D.InteriorPairing) (R : HexRegion) where
  
  heading : V → Fin 3 → ℤ
  
  hgeom : ∀ v j, D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j)
  
  headA : ℤ
  
  headL : ℤ
  
  headTp : ℤ
  
  headTm : ℤ
  
  headU : ℤ
  
  hHeadA : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
    heading e.vtx e.edge = headA
  
  hHeadL : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
    heading e.vtx e.edge = headL
  
  hHeadTp : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
    heading e.vtx e.edge = headTp
  
  hHeadTm : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
    heading e.vtx e.edge = headTm
  
  hHeadU : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
    heading e.vtx e.edge = headU
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  

  phaseA : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headA : ℝ) * Complex.I) * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  

  phaseL : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headL : ℝ) * Complex.I) * ((hexBdryCl * lam : ℝ) : ℂ)
  

  phaseTp : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTp : ℝ) * Complex.I) * ((hexBdryCt * taup : ℝ) : ℂ)
  

  phaseTm : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headTm : ℝ) * Complex.I) * ((hexBdryCt * taum : ℝ) : ℂ)
  

  phaseU : (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
        D.obs (D.mid e.vtx e.edge))
      = 2 * Complex.exp ((hexPhase_sideTilt headU : ℝ) * Complex.I) * ((ups : ℝ) : ℂ)

namespace HexPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexPhaseData D P R)












noncomputable def toRegionAssign : HexRegionAssign D P R where
  heading := H.heading
  hgeom := H.hgeom
  headA := H.headA
  headL := H.headL
  headTp := H.headTp
  headTm := H.headTm
  headU := H.headU
  hHeadA := H.hHeadA
  hHeadL := H.hHeadL
  hHeadTp := H.hHeadTp
  hHeadTm := H.hHeadTm
  hHeadU := H.hHeadU
  lam := H.lam
  taup := H.taup
  taum := H.taum
  ups := H.ups
  Fa := H.Fa
  projA := hexPhase_projA H.headA H.Fa H.phaseA
  projL := hexPhase_projL H.headL H.lam H.phaseL
  projTp := hexPhase_projTp H.headTp H.taup H.phaseTp
  projTm := hexPhase_projTm H.headTm H.taum H.phaseTm
  projU := hexPhase_projU H.headU H.ups H.phaseU

@[simp] theorem toRegionAssign_lam : H.toRegionAssign.lam = H.lam := rfl
@[simp] theorem toRegionAssign_taup : H.toRegionAssign.taup = H.taup := rfl
@[simp] theorem toRegionAssign_taum : H.toRegionAssign.taum = H.taum := rfl
@[simp] theorem toRegionAssign_ups : H.toRegionAssign.ups = H.ups := rfl
@[simp] theorem toRegionAssign_Fa : H.toRegionAssign.Fa = H.Fa := rfl

end HexPhaseData




























theorem hexPhase_identity {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
    (hsub : P.interior ⊆ D.incidences) (H : HexPhaseData D P R) (hFa : H.Fa = 1) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = 1 := by
  have h := hexBdryAssign_identity hsub H.toRegionAssign (by simpa using hFa)
  simpa using h











theorem hexPhase_identity_scales {D : ℕ → HexDomain V}
    {P : ∀ v, (D v).InteriorPairing} {R : ℕ → HexRegion}
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (H : ∀ v, HexPhaseData (D v) (P v) (R v))
    (hFa : ∀ v, 1 ≤ v → (H v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (H v).lam + hexBdryCt * ((H v).taup + (H v).taum) + (H v).ups = 1 := by
  intro v hv
  exact hexPhase_identity (hsub v) (H v) (hFa v hv)













theorem hexPhase_hexCell_normalForm (j : Fin 3) :
    hexUnit (2 * (j : ℤ))
      = Complex.I * Complex.exp ((-(hexPhase_sideTilt (2 * (j : ℤ))) : ℝ) * Complex.I) :=
  hexPhase_hexUnit_normalForm (2 * (j : ℤ))






theorem hexPhase_proj_fires (h : ℤ) (cmag : ℝ) :
    ((1 / 2 : ℂ) * hexUnit h)
        * (2 * Complex.exp ((hexPhase_sideTilt h : ℝ) * Complex.I) * (cmag : ℂ))
      = Complex.I * (cmag : ℂ) :=
  hexPhase_proj h cmag _ rfl

end StatMech.Universality
