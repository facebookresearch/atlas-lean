/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Code.Universality.HexContourDecomp
import Code.Universality.HexLattice

namespace StatMech.Universality

open Complex
open scoped BigOperators









theorem hexFam_omega_cube : hexOmega ^ 3 = 1 := by
  unfold hexOmega
  rw [← Complex.exp_nat_mul]
  rw [show ((3 : ℕ) : ℂ) * (↑(2 * Real.pi / 3) * Complex.I) = (2 * Real.pi : ℂ) * Complex.I by
        push_cast; ring]
  exact Complex.exp_two_pi_mul_I


theorem hexFam_omega_ne_one : hexOmega ≠ 1 := by
  unfold hexOmega
  intro h
  have hre := congrArg Complex.re h
  rw [show (↑(2 * Real.pi / 3) * Complex.I) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by
        push_cast; ring] at hre
  rw [Complex.exp_ofReal_mul_I_re] at hre
  simp only [Complex.one_re] at hre
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
    rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
        Real.cos_pi_div_three]
  rw [hcos] at hre; norm_num at hre






theorem hexFam_omega_sum_zero : (1 : ℂ) + hexOmega + hexOmega ^ 2 = 0 := by
  have factored : (hexOmega - 1) * (1 + hexOmega + hexOmega ^ 2) = hexOmega ^ 3 - 1 := by ring
  rw [hexFam_omega_cube, sub_self] at factored
  rcases mul_eq_zero.mp factored with h | h
  · exact absurd (sub_eq_zero.mp h) hexFam_omega_ne_one
  · exact h






theorem hexFam_hexUnit_add_two (h : ℤ) : hexUnit (h + 2) = hexUnit h * hexOmega := by
  unfold hexUnit hexOmega
  rw [← Complex.exp_add]; congr 1; push_cast; ring












theorem hexFam_part5 {V : Type*} [DecidableEq V]
    (s : Finset (HexIncidence V)) (cls : HexIncidence V → Fin 5) :
    s = (s.filter (fun e => cls e = 0)) ∪ (s.filter (fun e => cls e = 1)) ∪
        (s.filter (fun e => cls e = 2)) ∪ (s.filter (fun e => cls e = 3)) ∪
        (s.filter (fun e => cls e = 4)) := by
  ext e
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro he
    have hcase : cls e = 0 ∨ cls e = 1 ∨ cls e = 2 ∨ cls e = 3 ∨ cls e = 4 := by omega
    tauto
  · rintro ((((⟨he, _⟩ | ⟨he, _⟩) | ⟨he, _⟩) | ⟨he, _⟩) | ⟨he, _⟩) <;> exact he





theorem hexFam_disj5 {V : Type*} [DecidableEq V]
    (s : Finset (HexIncidence V)) (cls : HexIncidence V → Fin 5) (a b : Fin 5) (hab : a ≠ b) :
    Disjoint (s.filter (fun e => cls e = a)) (s.filter (fun e => cls e = b)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  simp only [Finset.mem_filter] at he1 he2
  exact hab (he1.2 ▸ he2.2)






















structure HexFamilyData {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) where
  
  cls : HexIncidence V → Fin 5
  
  dirA : ℂ
  
  dirL : ℂ
  
  dirTp : ℂ
  
  dirTm : ℂ
  
  dirU : ℂ
  
  dirEqA : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 0),
    D.mid e.vtx e.edge - D.pos e.vtx = dirA
  
  dirEqL : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 1),
    D.mid e.vtx e.edge - D.pos e.vtx = dirL
  
  dirEqTp : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 2),
    D.mid e.vtx e.edge - D.pos e.vtx = dirTp
  
  dirEqTm : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 3),
    D.mid e.vtx e.edge - D.pos e.vtx = dirTm
  
  dirEqU : ∀ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 4),
    D.mid e.vtx e.edge - D.pos e.vtx = dirU
  
  lam : ℝ
  
  taup : ℝ
  
  taum : ℝ
  
  ups : ℝ
  
  Fa : ℝ
  
  projA : dirA *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 0), D.obs (D.mid e.vtx e.edge))
      = Complex.I * (((-1 : ℝ) * Fa : ℝ) : ℂ)
  
  projL : dirL *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 1), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCl * lam : ℝ) : ℂ)
  
  projTp : dirTp *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 2), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taup : ℝ) : ℂ)
  
  projTm : dirTm *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 3), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((hexBdryCt * taum : ℝ) : ℂ)
  
  projU : dirU *
      (∑ e ∈ (D.incidences \ P.interior).filter (fun e => cls e = 4), D.obs (D.mid e.vtx e.edge))
      = Complex.I * ((ups : ℝ) : ℂ)

namespace HexFamilyData

variable {V : Type*} [DecidableEq V] {D : HexDomain V} {P : D.InteriorPairing}
  (F : HexFamilyData D P)









noncomputable def toDecomp : HexBoundaryDecomp D P where
  A := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 0), F.dirA, F.dirEqA⟩
  L := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 1), F.dirL, F.dirEqL⟩
  Tp := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 2), F.dirTp, F.dirEqTp⟩
  Tm := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 3), F.dirTm, F.dirEqTm⟩
  U := ⟨(D.incidences \ P.interior).filter (fun e => F.cls e = 4), F.dirU, F.dirEqU⟩
  lam := F.lam
  taup := F.taup
  taum := F.taum
  ups := F.ups
  Fa := F.Fa
  partition := hexFam_part5 (D.incidences \ P.interior) F.cls
  disjAL := hexFam_disj5 _ F.cls 0 1 (by decide)
  disjATp := hexFam_disj5 _ F.cls 0 2 (by decide)
  disjATm := hexFam_disj5 _ F.cls 0 3 (by decide)
  disjAU := hexFam_disj5 _ F.cls 0 4 (by decide)
  disjLTp := hexFam_disj5 _ F.cls 1 2 (by decide)
  disjLTm := hexFam_disj5 _ F.cls 1 3 (by decide)
  disjLU := hexFam_disj5 _ F.cls 1 4 (by decide)
  disjTpTm := hexFam_disj5 _ F.cls 2 3 (by decide)
  disjTpU := hexFam_disj5 _ F.cls 2 4 (by decide)
  disjTmU := hexFam_disj5 _ F.cls 3 4 (by decide)
  projA := F.projA
  projL := F.projL
  projTp := F.projTp
  projTm := F.projTm
  projU := F.projU

end HexFamilyData

















theorem hexFam_straightSide_dir {V : Type*} [DecidableEq V] (D : HexDomain V)
    (heading : V → Fin 3 → ℤ)
    (hgeom : ∀ v j, D.mid v j - D.pos v = (1 / 2 : ℂ) * hexUnit (heading v j))
    (s : Finset (HexIncidence V)) (h : ℤ)
    (hconst : ∀ e ∈ s, heading e.vtx e.edge = h) :
    ∀ e ∈ s, D.mid e.vtx e.edge - D.pos e.vtx = (1 / 2 : ℂ) * hexUnit h := by
  intro e he
  rw [hgeom e.vtx e.edge, hconst e he]













noncomputable def hexCell (c : ℂ) : HexDomain (Fin 1) where
  interiorVertices := {0}
  pos := fun _ => 0
  mid := fun _ j => (1 / 2 : ℂ) * hexUnit (2 * (j : ℤ))
  obs := fun _ => c
  relation := by
    intro v _
    have e2 : hexUnit (2 * ((1 : Fin 3) : ℤ)) = hexUnit 0 * hexOmega := by
      have hcast : (2 * ((1 : Fin 3) : ℤ)) = (0 : ℤ) + 2 := by decide
      rw [hcast]; exact hexFam_hexUnit_add_two 0
    have e4 : hexUnit (2 * ((2 : Fin 3) : ℤ)) = hexUnit 0 * hexOmega ^ 2 := by
      have h1 := hexFam_hexUnit_add_two 2
      have hcast : (2 * ((2 : Fin 3) : ℤ)) = (2 : ℤ) + 2 := by decide
      rw [hcast, h1, show hexUnit 2 = hexUnit 0 * hexOmega from by
            have h2 : (2 : ℤ) = 0 + 2 := by decide
            rw [h2]; exact hexFam_hexUnit_add_two 0]
      ring
    have e0 : hexUnit (2 * ((0 : Fin 3) : ℤ)) = hexUnit 0 := by norm_num
    rw [Fin.sum_univ_three, e0, e2, e4]
    have key : ((1 / 2 : ℂ) * hexUnit 0 - 0) * c
        + ((1 / 2 : ℂ) * (hexUnit 0 * hexOmega) - 0) * c
        + ((1 / 2 : ℂ) * (hexUnit 0 * hexOmega ^ 2) - 0) * c
        = (1 / 2 : ℂ) * hexUnit 0 * c * (1 + hexOmega + hexOmega ^ 2) := by ring
    rw [key, hexFam_omega_sum_zero, mul_zero]



theorem hexCell_geom (c : ℂ) (v : Fin 1) (j : Fin 3) :
    (hexCell c).mid v j - (hexCell c).pos v = (1 / 2 : ℂ) * hexUnit (2 * (j : ℤ)) := by
  simp only [hexCell, sub_zero]





theorem hexCell_straightSide (c : ℂ) (j0 : Fin 3) (s : Finset (HexIncidence (Fin 1)))
    (hconst : ∀ e ∈ s, e.edge = j0) :
    ∀ e ∈ s, (hexCell c).mid e.vtx e.edge - (hexCell c).pos e.vtx
      = (1 / 2 : ℂ) * hexUnit (2 * (j0 : ℤ)) := by
  refine hexFam_straightSide_dir (hexCell c) (fun _ j => 2 * (j : ℤ)) (hexCell_geom c) s
    (2 * (j0 : ℤ)) ?_
  intro e he
  rw [hconst e he]
























theorem hexBoundary_identity_via_family {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) (hsub : P.interior ⊆ D.incidences)
    (F : HexFamilyData D P) (hFa : F.Fa = 1) :
    hexBdryCl * F.lam + hexBdryCt * (F.taup + F.taum) + F.ups = 1 := by
  have h := hexBoundary_identity_via_decomp D P hsub F.toDecomp (by simpa using hFa)
  simpa using h









theorem hexBoundary_identity_scales_via_family {V : Type*} [DecidableEq V]
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (F : ∀ v, HexFamilyData (D v) (P v))
    (hFa : ∀ v, 1 ≤ v → (F v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (F v).lam + hexBdryCt * ((F v).taup + (F v).taum) + (F v).ups = 1 := by
  intro v hv
  exact hexBoundary_identity_via_family (D v) (P v) (hsub v) (F v) (hFa v hv)

end StatMech.Universality
