/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexInfraWinding
import Code.Universality.HexInfraHeading
import Code.Universality.HexW1Sides

namespace StatMech.Universality

open HexWalk List Complex
open scoped BigOperators Real










theorem hexW1Exit_halfStep_add_three (h : ℤ) :
    HexWalk.halfStep (h + 3) = - HexWalk.halfStep h := by
  unfold HexWalk.halfStep
  rw [hexUnit_add_three]; ring













theorem hexW1Exit_penult_mem (m : ℂ) (h : ℤ) (t : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h (t :: ts) - HexWalk.halfStep (hexInfra_headAccum h (t :: ts))
      ∈ HexWalk.verticesAux m h (t :: ts) := by
  induction ts generalizing m h t with
  | nil =>
    rw [hexInfra_midAccum_cons, hexInfra_midAccum_nil, hexInfra_headAccum_cons,
      hexInfra_headAccum_nil, HexWalk.verticesAux_cons]
    have : m + HexWalk.halfStep h + HexWalk.halfStep (h + t) - HexWalk.halfStep (h + t)
        = m + HexWalk.halfStep h := by ring
    rw [this]
    exact List.mem_cons_self
  | cons s ss ih =>
    rw [HexWalk.verticesAux_cons]
    refine List.mem_cons_of_mem _ ?_
    have key : hexInfra_midAccum m h (t :: s :: ss)
          - HexWalk.halfStep (hexInfra_headAccum h (t :: s :: ss))
        = hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) (s :: ss)
          - HexWalk.halfStep (hexInfra_headAccum (h + t) (s :: ss)) := by
      rw [hexInfra_midAccum_cons, hexInfra_headAccum_cons]
    rw [key]
    exact ih (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) s


theorem hexW1Exit_halfStep_ne_zero (h : ℤ) : HexWalk.halfStep h ≠ 0 := by
  unfold HexWalk.halfStep
  exact mul_ne_zero (by norm_num) (hexUnit_ne_zero h)




theorem hexW1Exit_penult_eq_of_endsAt (a : ℂ) (h0 : ℤ) (z : ℂ) (t : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ∈ (HexWalk.ofTurns a h0 (t :: ts)).vertices := by
  have hzm : hexInfra_midAccum a h0 (t :: ts) = z := by
    rw [← hexInfra_endMid_eq_midAccum]; exact hz
  rw [← hzm]
  exact hexW1Exit_penult_mem a h0 t ts




theorem hexW1Exit_penult_ne_last (z : ℂ) (H : ℤ) :
    z - HexWalk.halfStep H ≠ z + HexWalk.halfStep H := by
  intro hc
  have : HexWalk.halfStep H + HexWalk.halfStep H = 0 := by linear_combination -hc
  have h2 : (2 : ℂ) * HexWalk.halfStep H = 0 := by linear_combination this
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact hexW1Exit_halfStep_ne_zero H h











theorem hexW1Exit_lastVertex_eq_iff (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
        = z + HexWalk.halfStep H)
      ↔ HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H := by
  have hzm : hexInfra_midAccum a h0 ts = z := by
    rw [← hexInfra_endMid_eq_midAccum]; exact hz
  rw [hzm]
  constructor
  · intro h; exact add_left_cancel h
  · intro h; rw [h]




theorem hexW1Exit_lastVertex_of_dir (a : ℂ) (h0 : ℤ) (z : ℂ) (H : ℤ) (ts : List ℤ)
    (hz : (HexWalk.ofTurns a h0 ts).EndsAt z)
    (hdir : HexWalk.halfStep (hexInfra_headAccum h0 ts) = HexWalk.halfStep H) :
    hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)
      = z + HexWalk.halfStep H :=
  (hexW1Exit_lastVertex_eq_iff a h0 z H ts hz).mpr hdir





























structure HexStraightSide (inRegion interior : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) where
  
  H : ℤ
  

  uniqueInterior : ∀ h : ℤ, interior (z + HexWalk.halfStep h)
      → HexWalk.halfStep h = HexWalk.halfStep (H + 3)
  


  interiorVertices : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → ∀ v ∈ (HexWalk.ofTurns a h0 ts).vertices,
          v ≠ z + HexWalk.halfStep (hexInfra_headAccum h0 ts) → interior v

namespace HexStraightSide

variable {inRegion interior : ℂ → Prop} {a : ℂ} {h0 : ℤ} {z : ℂ}
    (S : HexStraightSide inRegion interior a h0 z)








theorem dir_eq (t : ℤ) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) = HexWalk.halfStep S.H := by
  
  have hmem : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ∈ (HexWalk.ofTurns a h0 (t :: ts)).vertices :=
    hexW1Exit_penult_eq_of_endsAt a h0 z t ts hadm.2.2
  
  have hne : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      ≠ z + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts)) :=
    hexW1Exit_penult_ne_last z (hexInfra_headAccum h0 (t :: ts))
  
  have hpen : interior (z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))) :=
    S.interiorVertices (t :: ts) hadm _ hmem hne
  
  have heq : z - HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      = z + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts) + 3) := by
    rw [hexW1Exit_halfStep_add_three]; ring
  rw [heq] at hpen
  
  have hu := S.uniqueInterior (hexInfra_headAccum h0 (t :: ts) + 3) hpen
  
  rw [hexW1Exit_halfStep_add_three, hexW1Exit_halfStep_add_three] at hu
  exact neg_injective hu





theorem side_exit (t : ℤ) (ts : List ℤ)
    (hadm : (HexWalk.ofTurns a h0 (t :: ts)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).StaysIn inRegion
      ∧ (HexWalk.ofTurns a h0 (t :: ts)).EndsAt z) :
    hexInfra_midAccum a h0 (t :: ts) + HexWalk.halfStep (hexInfra_headAccum h0 (t :: ts))
      = z + HexWalk.halfStep S.H :=
  hexW1Exit_lastVertex_of_dir a h0 z S.H (t :: ts) hadm.2.2 (S.dir_eq t ts hadm)

end HexStraightSide




















noncomputable def hexW1Exit_boundarySide (inRegion interior : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (S : HexStraightSide inRegion interior a h0 z) (w : ℤ) (hHL : w ≤ S.H) (hHU : S.H < w + 6)
    (hwin : ∀ ts : List ℤ, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
      → w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6)
    (htrivial : ([] : List ℤ) ∈ ({ts : List ℤ |
        (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z} : Set (List ℤ))
      → hexInfra_midAccum a h0 [] + HexWalk.halfStep (hexInfra_headAccum h0 [])
          = z + HexWalk.halfStep S.H) :
    HexBoundarySide inRegion a h0 z where
  H := S.H
  w := w
  hHL := hHL
  hHU := hHU
  exits := by
    intro ts hadm
    refine ⟨?_, hwin ts hadm⟩
    cases ts with
    | nil => exact htrivial hadm
    | cons t ts => exact S.side_exit t ts hadm















theorem hexW1Exit_singleton_uniqueInterior (a : ℂ) (h0 : ℤ) (h : ℤ)
    (hint : (fun m => m = a + HexWalk.halfStep h0) (a + HexWalk.halfStep h)) :
    HexWalk.halfStep h = HexWalk.halfStep ((h0 + 3) + 3) := by
  
  have hstep : HexWalk.halfStep h = HexWalk.halfStep h0 := add_left_cancel hint
  
  have hper : HexWalk.halfStep ((h0 + 3) + 3) = HexWalk.halfStep h0 := by
    rw [show ((h0 + 3) + 3 : ℤ) = h0 + 6 by ring]
    unfold HexWalk.halfStep; rw [hexUnit_add_six]
  rw [hstep, hper]














noncomputable def hexW1Exit_singleton_straightSide (a : ℂ) (h0 : ℤ) :
    HexStraightSide (fun m => m = a) (fun m => m = a + HexWalk.halfStep h0) a h0 a where
  H := h0 + 3
  uniqueInterior := fun h hint => hexW1Exit_singleton_uniqueInterior a h0 h hint
  interiorVertices := by
    intro ts hadm v hv hvne
    
    have hnil : ts = [] := hexW1_singleton_admissible_nil a h0 ts hadm
    subst hnil
    
    rw [hexInfra_headAccum_nil] at hvne
    have hverts : (HexWalk.ofTurns a h0 ([] : List ℤ)).vertices = [a + HexWalk.halfStep h0] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts, List.mem_singleton] at hv
    exact absurd hv hvne




theorem hexW1Exit_singleton_inner_eq (a : ℂ) (h0 : ℤ) :
    a - HexWalk.halfStep ((h0 + 3 : ℤ)) = a + HexWalk.halfStep h0 := by
  rw [hexW1Exit_halfStep_add_three]; ring














theorem hexW1Exit_mids_singleRight (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).mids
      = [a, a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))] := by
  unfold HexWalk.ofTurns HexWalk.mids; simp [HexWalk.midsAux]



theorem hexW1Exit_singleRight_legal (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht; simp only [HexWalk.ofTurns_turns, List.mem_singleton] at ht; exact Or.inr ht
  · unfold HexWalk.IsSAW HexWalk.vertices HexWalk.ofTurns
    simp only [HexWalk.verticesAux]
    rw [List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro heq
    have h2 : (2 : ℂ) * HexWalk.halfStep (h0 + (-1)) = 0 := by linear_combination -heq
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact hexW1Exit_halfStep_ne_zero (h0 + (-1)) h


theorem hexW1Exit_singleRight_endsAt (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).EndsAt
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
  unfold HexWalk.EndsAt HexWalk.endMid HexWalk.ofTurns HexWalk.mids; simp [HexWalk.midsAux]


theorem hexW1Exit_singleRight_staysIn (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn
      (fun m => m = a ∨ m = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
  intro m hm
  rw [hexW1Exit_mids_singleRight] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact hm







noncomputable def hexW1Exit_singleRight_straightSide (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)]) :
    HexStraightSide inReg (fun v => v = a + HexWalk.halfStep h0) a h0
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) where
  H := h0 - 1
  uniqueInterior := by
    intro h hint
    have hh : HexWalk.halfStep h = - HexWalk.halfStep (h0 + (-1)) := by linear_combination hint
    rw [hh, show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexW1Exit_halfStep_add_three]
  interiorVertices := by
    intro ts hadm v hv hvne
    have hts : ts = [(-1 : ℤ)] := hclass ts hadm
    subst hts
    have hverts : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).vertices
        = [a + HexWalk.halfStep h0,
            a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) + HexWalk.halfStep (h0 + (-1))] := by
      unfold HexWalk.ofTurns HexWalk.vertices; simp [HexWalk.verticesAux]
    rw [hverts] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h
    · exact h
    · exfalso; apply hvne
      rw [h, hexInfra_headAccum_cons, hexInfra_headAccum_nil,
        show (h0 + (-1) : ℤ) = h0 + (-1) from rfl]






theorem hexW1Exit_singleRight_dir_eq_fires (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
      = HexWalk.halfStep ((hexW1Exit_singleRight_straightSide a h0 inReg hclass).H) :=
  (hexW1Exit_singleRight_straightSide a h0 inReg hclass).dir_eq (-1) []
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩




theorem hexW1Exit_singleRight_side_exit_fires (a : ℂ) (h0 : ℤ) (inReg : ℂ → Prop)
    (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt
            (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
    (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
    hexInfra_midAccum a h0 [(-1 : ℤ)] + HexWalk.halfStep (hexInfra_headAccum h0 [(-1 : ℤ)])
      = (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)))
        + HexWalk.halfStep ((hexW1Exit_singleRight_straightSide a h0 inReg hclass).H) :=
  (hexW1Exit_singleRight_straightSide a h0 inReg hclass).side_exit (-1) []
    ⟨hexW1Exit_singleRight_legal a h0, hstay, hexW1Exit_singleRight_endsAt a h0⟩

end StatMech.Universality
