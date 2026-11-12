/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexW1ExitGeom

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real












def hexIncident (v m : ℂ) (d : ℤ) : Prop :=
  v = m + HexWalk.halfStep d ∨ v = m + HexWalk.halfStep (d + 3)





def hexStripInterior (dregion : ℂ → ℤ → Prop) (v : ℂ) : Prop :=
  ∃ (m1 m2 : ℂ) (d1 d2 : ℤ), dregion m1 d1 ∧ dregion m2 d2 ∧ (m1, d1) ≠ (m2, d2)
    ∧ hexIncident v m1 d1 ∧ hexIncident v m2 d2









noncomputable def hexStripDirMids (m : ℂ) (h : ℤ) : List ℤ → List (ℂ × ℤ)
  | [] => [(m, h)]
  | t :: ts =>
      (m, h) :: hexStripDirMids (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts

@[simp] theorem hexStripDirMids_nil (m : ℂ) (h : ℤ) : hexStripDirMids m h [] = [(m, h)] := rfl

@[simp] theorem hexStripDirMids_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    hexStripDirMids m h (t :: ts)
      = (m, h) :: hexStripDirMids (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts :=
  rfl







theorem hexStrip_nonlast_dir (m : ℂ) (h : ℤ) (ts : List ℤ) (v : ℂ)
    (hv : v ∈ HexWalk.verticesAux m h ts)
    (hvne : v ≠ hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) :
    ∃ (m' : ℂ) (h' t' : ℤ),
        (m', h') ∈ hexStripDirMids m h ts
      ∧ (m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t'), h' + t')
          ∈ hexStripDirMids m h ts
      ∧ v = m' + HexWalk.halfStep h'
      ∧ t' ∈ ts := by
  induction ts generalizing m h with
  | nil =>
    rw [HexWalk.verticesAux_nil, List.mem_singleton] at hv
    rw [hexInfra_midAccum_nil, hexInfra_headAccum_nil] at hvne
    exact absurd hv hvne
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, List.mem_cons] at hv
    rcases hv with hhead | htail
    · 
      refine ⟨m, h, t, ?_, ?_, hhead, List.mem_cons_self⟩
      · rw [hexStripDirMids_cons]; exact List.mem_cons_self
      · rw [hexStripDirMids_cons]
        refine List.mem_cons_of_mem _ ?_
        cases ts with
        | nil => rw [hexStripDirMids_nil]; exact List.mem_singleton.mpr rfl
        | cons s ss => rw [hexStripDirMids_cons]; exact List.mem_cons_self
    · 
      rw [hexInfra_midAccum_cons, hexInfra_headAccum_cons] at hvne
      obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ := ih _ _ htail hvne
      refine ⟨m', h', t', ?_, ?_, hveq, List.mem_cons_of_mem _ ht'⟩
      · rw [hexStripDirMids_cons]; exact List.mem_cons_of_mem _ hm1
      · rw [hexStripDirMids_cons]; exact List.mem_cons_of_mem _ hm2










def hexStripStaysInDir (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ) : Prop :=
  ∀ p ∈ hexStripDirMids a h0 ts, dregion p.1 p.2














theorem hexStrip_interiorVertices_core (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
    (hstay : hexStripStaysInDir dregion a h0 ts)
    (v : ℂ) (hv : v ∈ (HexWalk.ofTurns a h0 ts).vertices)
    (hvne : v ≠ hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)) :
    hexStripInterior dregion v := by
  have hvv : v ∈ HexWalk.verticesAux a h0 ts := hv
  obtain ⟨m', h', t', hm1, hm2, hveq, ht'⟩ := hexStrip_nonlast_dir a h0 ts v hvv hvne
  have hr1 : dregion m' h' := hstay (m', h') hm1
  have hr2 : dregion (m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t')) (h' + t') :=
    hstay _ hm2
  have htlegal : t' = 1 ∨ t' = -1 := hlegal.1 t' (by unfold HexWalk.ofTurns; exact ht')
  refine ⟨m', m' + HexWalk.halfStep h' + HexWalk.halfStep (h' + t'),
    h', h' + t', hr1, hr2, ?_, ?_, ?_⟩
  · 
    
    intro hc
    rw [Prod.mk.injEq] at hc
    have hzero : HexWalk.halfStep h' + HexWalk.halfStep (h' + t') = 0 := by
      have : m' + (HexWalk.halfStep h' + HexWalk.halfStep (h' + t')) = m' + 0 := by
        rw [add_zero, ← add_assoc]; exact hc.1.symm
      exact add_left_cancel this
    exact hexW1_halfStep_add_ne_zero h' t' htlegal hzero
  · 
    left; exact hveq
  · 
    right; rw [hexW1Exit_halfStep_add_three, hveq]; ring
















noncomputable def hexStrip_straightSide (dregion : ℂ → ℤ → Prop) (inRegion : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (z : ℂ) (Hd : ℤ)
    (huniq : ∀ h : ℤ, hexStripInterior dregion (z + HexWalk.halfStep h)
        → HexWalk.halfStep h = HexWalk.halfStep (Hd + 3))
    (hbridge : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → hexStripStaysInDir dregion a h0 ts) :
    HexStraightSide inRegion (hexStripInterior dregion) a h0 z where
  H := Hd
  uniqueInterior := huniq
  interiorVertices := by
    intro ts hadm v hv hvne
    have hzm : hexInfra_midAccum a h0 ts = z := by
      rw [← hexInfra_endMid_eq_midAccum]; exact hadm.2.2
    refine hexStrip_interiorVertices_core dregion a h0 ts hadm.1 (hbridge ts hadm) v hv ?_
    rw [hzm]; exact hvne









theorem hexStrip_halfStep_re (h : ℤ) :
    (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]; norm_num


theorem hexStrip_halfStep_im (h : ℤ) :
    (HexWalk.halfStep h).im = (1 / 2) * Real.sin (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]; norm_num


theorem hexStrip_normSq_halfStep (h : ℤ) : Complex.normSq (HexWalk.halfStep h) = 1 / 4 := by
  rw [Complex.normSq_apply, hexStrip_halfStep_re, hexStrip_halfStep_im]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 6 + (h : ℝ) * (Real.pi / 3))]




theorem hexStrip_normSq_two_one (h0 : ℤ) :
    Complex.normSq (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) = 7 / 4 := by
  have hre : (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))).re
      = 2 * (HexWalk.halfStep h0).re + (HexWalk.halfStep (h0 + (-1))).re := by
    simp [Complex.add_re, Complex.mul_re]
  have him : (2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))).im
      = 2 * (HexWalk.halfStep h0).im + (HexWalk.halfStep (h0 + (-1))).im := by
    simp [Complex.add_im, Complex.mul_im]
  rw [Complex.normSq_apply, hre, him,
    hexStrip_halfStep_re, hexStrip_halfStep_im, hexStrip_halfStep_re, hexStrip_halfStep_im]
  have hB : (Real.pi / 6 + ((h0 + (-1) : ℤ) : ℝ) * (Real.pi / 3))
      = (Real.pi / 6 + (h0 : ℝ) * (Real.pi / 3)) - Real.pi / 3 := by push_cast; ring
  rw [hB]
  set A := Real.pi / 6 + (h0 : ℝ) * (Real.pi / 3) with hA
  rw [Real.cos_sub, Real.sin_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sin_sq_add_cos_sq A, hsqrt]




theorem hexStrip_two_one_add_ne_zero (h0 h : ℤ) :
    2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) + HexWalk.halfStep h ≠ 0 := by
  intro hc
  have heq : 2 * HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) = - HexWalk.halfStep h := by
    linear_combination hc
  have h1 := hexStrip_normSq_two_one h0
  rw [heq, Complex.normSq_neg, hexStrip_normSq_halfStep] at h1
  norm_num at h1





theorem hexStrip_outer_ne (a : ℂ) (h0 h : ℤ) :
    a + HexWalk.halfStep (h0 + 3)
      ≠ (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h := by
  intro hc
  rw [hexW1Exit_halfStep_add_three] at hc
  exact hexStrip_two_one_add_ne_zero h0 h (by linear_combination -hc)











def hexStrip_singleRightDReg (a : ℂ) (h0 : ℤ) : ℂ → ℤ → Prop :=
  fun m d => (m = a ∧ d = h0)
    ∨ (m = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) ∧ d = h0 + (-1))


theorem hexStrip_singleRight_dirMids (a : ℂ) (h0 : ℤ) :
    hexStripDirMids a h0 [(-1 : ℤ)]
      = [(a, h0), (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)), h0 + (-1))] := by
  rw [hexStripDirMids_cons, hexStripDirMids_nil]


theorem hexStrip_singleRight_staysInDir (a : ℂ) (h0 : ℤ) :
    hexStripStaysInDir (hexStrip_singleRightDReg a h0) a h0 [(-1 : ℤ)] := by
  intro p hp
  rw [hexStrip_singleRight_dirMids] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩





theorem hexStrip_singleRight_interior_fires (a : ℂ) (h0 : ℤ) :
    hexStripInterior (hexStrip_singleRightDReg a h0) (a + HexWalk.halfStep h0) := by
  apply hexStrip_interiorVertices_core (hexStrip_singleRightDReg a h0) a h0 [(-1 : ℤ)]
    (hexW1Exit_singleRight_legal a h0) (hexStrip_singleRight_staysInDir a h0)
  · 
    have hverts : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).vertices
        = [a + HexWalk.halfStep h0,
            a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))
              + HexWalk.halfStep (h0 + (-1))] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts]; exact List.mem_cons_self
  · 
    have hlast : hexInfra_midAccum a h0 [(-1 : ℤ)]
          + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
        = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))
            + HexWalk.halfStep (h0 + (-1)) := by
      simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil, hexInfra_headAccum_cons,
        hexInfra_headAccum_nil]
    rw [hlast]
    intro hc
    have h2 : (2 : ℂ) * HexWalk.halfStep (h0 + (-1)) = 0 := by linear_combination -hc
    rcases mul_eq_zero.mp h2 with hh | hh
    · norm_num at hh
    · exact hexW1Exit_halfStep_ne_zero (h0 + (-1)) hh







theorem hexStrip_singleRight_uniqueInterior (a : ℂ) (h0 : ℤ) (h : ℤ)
    (hint : hexStripInterior (hexStrip_singleRightDReg a h0)
      ((a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) + HexWalk.halfStep h)) :
    HexWalk.halfStep h = HexWalk.halfStep ((h0 - 1) + 3) := by
  set z := a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) with hzdef
  obtain ⟨m1, m2, d1, d2, hr1, hr2, hne, hi1, hi2⟩ := hint
  
  have key : hexIncident (z + HexWalk.halfStep h) a h0
      → HexWalk.halfStep h = HexWalk.halfStep ((h0 - 1) + 3) := by
    intro hi
    rcases hi with hi | hi
    · rw [hzdef] at hi
      rw [show ((h0 - 1) + 3 : ℤ) = (h0 + (-1)) + 3 by ring, hexW1Exit_halfStep_add_three]
      linear_combination hi
    · rw [hzdef] at hi; exact absurd hi.symm (hexStrip_outer_ne a h0 h)
  
  unfold hexStrip_singleRightDReg at hr1 hr2
  rcases hr1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact key hi1
  · rcases hr2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key hi2
    · exact absurd rfl hne









noncomputable def hexStrip_singleRight_straightSide (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStraightSide inReg (hexStripInterior (hexStrip_singleRightDReg a h0)) a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) :=
  hexStrip_straightSide (hexStrip_singleRightDReg a h0) inReg a h0
    (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) (h0 - 1)
    (hexStrip_singleRight_uniqueInterior a h0)
    (fun ts hadm => by
      have hts : ts = [(-1 : ℤ)] := hclass ts hadm
      subst hts; exact hexStrip_singleRight_staysInDir a h0)





theorem hexStrip_singleRight_side_exit_fires (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    hexInfra_midAccum a h0 [(-1 : ℤ)] + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
      = (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)))
        + HexWalk.halfStep ((hexStrip_singleRight_straightSide a h0 inReg hclass).H) :=
  (hexStrip_singleRight_straightSide a h0 inReg hclass).side_exit (-1) []
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩

end StatMech.Universality
