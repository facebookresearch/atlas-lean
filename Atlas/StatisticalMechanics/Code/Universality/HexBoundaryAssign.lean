/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Code.Universality.HexFamilyAssign

namespace StatMech.Universality

open Complex
open scoped BigOperators



















structure HexRegion where
  
  width : ℝ
  
  slant : ℝ
  
  start : ℂ
























noncomputable def hexRegionCls (R : HexRegion) (z : ℂ) : Fin 5 :=
  if z = R.start then 0
  else if z.re = 0 then 1
  else if z.re = R.width then 4
  else if Real.sqrt 3 * z.im = R.slant + z.re then 2
  else if Real.sqrt 3 * z.im = -(R.slant + z.re) then 3
  else 0


@[simp]
theorem hexRegionCls_start (R : HexRegion) : hexRegionCls R R.start = 0 := by
  unfold hexRegionCls; rw [if_pos rfl]



theorem hexRegionCls_left (R : HexRegion) {z : ℂ} (hz : z.re = 0)
    (hne : z ≠ R.start) : hexRegionCls R z = 1 := by
  unfold hexRegionCls; rw [if_neg hne, if_pos hz]



theorem hexRegionCls_right (R : HexRegion) {z : ℂ} (hz : z.re = R.width)
    (hne : z ≠ R.start) (hl : z.re ≠ 0) : hexRegionCls R z = 4 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_pos hz]



theorem hexRegionCls_topslant (R : HexRegion) {z : ℂ}
    (hz : Real.sqrt 3 * z.im = R.slant + z.re)
    (hne : z ≠ R.start) (hl : z.re ≠ 0) (hr : z.re ≠ R.width) :
    hexRegionCls R z = 2 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_neg hr, if_pos hz]




theorem hexRegionCls_botslant (R : HexRegion) {z : ℂ}
    (hz : Real.sqrt 3 * z.im = -(R.slant + z.re))
    (hne : z ≠ R.start) (hl : z.re ≠ 0) (hr : z.re ≠ R.width)
    (ht : Real.sqrt 3 * z.im ≠ R.slant + z.re) :
    hexRegionCls R z = 3 := by
  unfold hexRegionCls; rw [if_neg hne, if_neg hl, if_neg hr, if_neg ht, if_pos hz]










theorem hexRegionCls_eq_one_iff (R : HexRegion) (z : ℂ) :
    hexRegionCls R z = 1 ↔ z.re = 0 ∧ z ≠ R.start := by
  constructor
  · intro h
    unfold hexRegionCls at h
    by_cases h0 : z = R.start
    · rw [if_pos h0] at h; exact absurd h (by decide)
    · rw [if_neg h0] at h
      by_cases h1 : z.re = 0
      · exact ⟨h1, h0⟩
      · rw [if_neg h1] at h
        by_cases h2 : z.re = R.width
        · rw [if_pos h2] at h; exact absurd h (by decide)
        · rw [if_neg h2] at h
          by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
          · rw [if_pos h3] at h; exact absurd h (by decide)
          · rw [if_neg h3] at h
            by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
            · rw [if_pos h4] at h; exact absurd h (by decide)
            · rw [if_neg h4] at h; exact absurd h (by decide)
  · rintro ⟨hz, hne⟩; exact hexRegionCls_left R hz hne




theorem hexRegionCls_eq_four_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 4) : z.re = R.width := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · exact h2
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · rw [if_pos h3] at h; exact absurd h (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · rw [if_pos h4] at h; exact absurd h (by decide)
          · rw [if_neg h4] at h; exact absurd h (by decide)




theorem hexRegionCls_eq_two_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 2) : Real.sqrt 3 * z.im = R.slant + z.re := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · rw [if_pos h2] at h; exact absurd h (by decide)
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · exact h3
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · rw [if_pos h4] at h; exact absurd h (by decide)
          · rw [if_neg h4] at h; exact absurd h (by decide)




theorem hexRegionCls_eq_three_imp (R : HexRegion) (z : ℂ)
    (h : hexRegionCls R z = 3) : Real.sqrt 3 * z.im = -(R.slant + z.re) := by
  unfold hexRegionCls at h
  by_cases h0 : z = R.start
  · rw [if_pos h0] at h; exact absurd h (by decide)
  · rw [if_neg h0] at h
    by_cases h1 : z.re = 0
    · rw [if_pos h1] at h; exact absurd h (by decide)
    · rw [if_neg h1] at h
      by_cases h2 : z.re = R.width
      · rw [if_pos h2] at h; exact absurd h (by decide)
      · rw [if_neg h2] at h
        by_cases h3 : Real.sqrt 3 * z.im = R.slant + z.re
        · rw [if_pos h3] at h; exact absurd h (by decide)
        · rw [if_neg h3] at h
          by_cases h4 : Real.sqrt 3 * z.im = -(R.slant + z.re)
          · exact h4
          · rw [if_neg h4] at h; exact absurd h (by decide)





theorem hexRegionCls_start_eq_zero (R : HexRegion) : hexRegionCls R R.start = 0 :=
  hexRegionCls_start R







variable {V : Type*} [DecidableEq V]







noncomputable def hexRegionClsInc (R : HexRegion) (D : HexDomain V)
    (e : HexIncidence V) : Fin 5 :=
  hexRegionCls R (D.mid e.vtx e.edge)



























structure HexRegionAssign (D : HexDomain V) (P : D.InteriorPairing) (R : HexRegion) where
  
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
  
  projA : ((1 / 2 : ℂ) * hexUnit headA) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 0),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  
  projL : ((1 / 2 : ℂ) * hexUnit headL) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 1),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ)
  
  projTp : ((1 / 2 : ℂ) * hexUnit headTp) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 2),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ)
  
  projTm : ((1 / 2 : ℂ) * hexUnit headTm) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 3),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ)
  
  projU : ((1 / 2 : ℂ) * hexUnit headU) *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => hexRegionClsInc R D e = 4),
        D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((ups : ℝ) : ℂ)

namespace HexRegionAssign

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (A : HexRegionAssign D P R)









noncomputable def toFamilyData : HexFamilyData D P where
  cls := hexRegionClsInc R D
  dirA := (1 / 2 : ℂ) * hexUnit A.headA
  dirL := (1 / 2 : ℂ) * hexUnit A.headL
  dirTp := (1 / 2 : ℂ) * hexUnit A.headTp
  dirTm := (1 / 2 : ℂ) * hexUnit A.headTm
  dirU := (1 / 2 : ℂ) * hexUnit A.headU
  dirEqA := hexFam_straightSide_dir D A.heading A.hgeom _ A.headA A.hHeadA
  dirEqL := hexFam_straightSide_dir D A.heading A.hgeom _ A.headL A.hHeadL
  dirEqTp := hexFam_straightSide_dir D A.heading A.hgeom _ A.headTp A.hHeadTp
  dirEqTm := hexFam_straightSide_dir D A.heading A.hgeom _ A.headTm A.hHeadTm
  dirEqU := hexFam_straightSide_dir D A.heading A.hgeom _ A.headU A.hHeadU
  lam := A.lam
  taup := A.taup
  taum := A.taum
  ups := A.ups
  Fa := A.Fa
  projA := A.projA
  projL := A.projL
  projTp := A.projTp
  projTm := A.projTm
  projU := A.projU







noncomputable def toDecomp : HexBoundaryDecomp D P := A.toFamilyData.toDecomp

@[simp] theorem toFamilyData_lam : A.toFamilyData.lam = A.lam := rfl
@[simp] theorem toFamilyData_taup : A.toFamilyData.taup = A.taup := rfl
@[simp] theorem toFamilyData_taum : A.toFamilyData.taum = A.taum := rfl
@[simp] theorem toFamilyData_ups : A.toFamilyData.ups = A.ups := rfl
@[simp] theorem toFamilyData_Fa : A.toFamilyData.Fa = A.Fa := rfl

end HexRegionAssign


















noncomputable def hexBdryAssign_decomp {D : HexDomain V} {P : D.InteriorPairing}
    {R : HexRegion} (A : HexRegionAssign D P R) : HexBoundaryDecomp D P :=
  A.toDecomp


















theorem hexBdryAssign_identity {D : HexDomain V} {P : D.InteriorPairing}
    {R : HexRegion} (hsub : P.interior ⊆ D.incidences)
    (A : HexRegionAssign D P R) (hFa : A.Fa = 1) :
    hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = 1 := by
  have h := hexBoundary_identity_via_family D P hsub A.toFamilyData (by simpa using hFa)
  simpa using h









theorem hexBdryAssign_identity_scales {D : ℕ → HexDomain V}
    {P : ∀ v, (D v).InteriorPairing} {R : ℕ → HexRegion}
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (A : ∀ v, HexRegionAssign (D v) (P v) (R v))
    (hFa : ∀ v, 1 ≤ v → (A v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (A v).lam + hexBdryCt * ((A v).taup + (A v).taum) + (A v).ups = 1 := by
  intro v hv
  exact hexBdryAssign_identity (hsub v) (A v) (hFa v hv)




















theorem hexCell_mid_zero_re (c : ℂ) :
    ((hexCell c).mid (0 : Fin 1) (0 : Fin 3)).re = Real.sqrt 3 / 4 := by
  show ((1 / 2 : ℂ) * hexUnit (2 * ((0 : Fin 3) : ℤ))).re = Real.sqrt 3 / 4
  have hh : (2 * ((0 : Fin 3) : ℤ)) = (0 : ℤ) := by decide
  rw [hh]
  have e0 : hexUnit (0 : ℤ) = Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit; congr 1; push_cast; ring
  rw [e0, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_six]
  simp; ring



theorem hexCell_mid_two_re (c : ℂ) :
    ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)).re = 0 := by
  show ((1 / 2 : ℂ) * hexUnit (2 * ((2 : Fin 3) : ℤ))).re = 0
  have hh : (2 * ((2 : Fin 3) : ℤ)) = (4 : ℤ) := by decide
  rw [hh]
  have e4 : hexUnit (4 : ℤ) = Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    unfold hexUnit; congr 1; push_cast; ring
  rw [e4, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp









theorem hexRegionCls_hexCell_two (c : ℂ) (R : HexRegion)
    (hne : (hexCell c).mid (0 : Fin 1) (2 : Fin 3) ≠ R.start) :
    hexRegionCls R ((hexCell c).mid (0 : Fin 1) (2 : Fin 3)) = 1 :=
  hexRegionCls_left R (hexCell_mid_two_re c) hne

end StatMech.Universality
