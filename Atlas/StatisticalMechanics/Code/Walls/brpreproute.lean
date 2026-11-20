/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Walls.bcrboxrep
import Code.Walls.brtrouteclose

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}












theorem brp_trifForestData_of_repRoute (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxtri : bc67_IsGnTrifurcation ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
    (hroute : bcr_RepRoute ω L x a) :
    bgc_TrifForestData ω L R :=
  bgc_trifForestData_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj hsep hroute
















theorem brp_tail_survives_boxes (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x arm : Site d)
    (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, r k ∉ T) ∧
        (∀ k, (bc67_contractedLattice ω L x).Adj (r k) (r (k + 1))) ∧
        (∀ z : Site d, bc61_boxAround d L z ⊆ T →
          ∀ k, (bc67_contractedLattice ω L z).Reachable b (r k)) := by
  obtain ⟨b, hreach, r, hr0, hinj, hadj, havoid⟩ :=
    bar_boxAvoiding_armRay ω L x arm hinf T
  refine ⟨b, hreach, r, hr0, hinj, havoid, hadj, ?_⟩
  intro z hzT k
  
  have havoidz : ∀ m, r m ∉ bc61_boxAround d L z := fun m hm => havoid m (hzT hm)
  have := brt_ray_reach ω L x z r hadj havoidz k
  rwa [hr0] at this












theorem brp_repRoute_of_entry (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    (tip b : Fin 3 → Site d)
    (hentry : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i))
    (htail : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) :
    bcr_RepRoute ω L x tip := by
  intro i j hij
  exact (hentry i j hij).trans (htail i j hij)












theorem brp_off_box_coord {L : ℕ} {z p : Site 2} (i : Fin 2) (h : L < ((p - z) i).natAbs) :
    p ∉ bc61_boxAround 2 L z := by
  rw [bc61_mem_boxAround, mem_box]; push Not; exact ⟨i, h⟩



theorem brp_cross_hreach_avoid (L : ℕ) (z : Site 2) (c : ℤ) (j : ℕ)
    (hoff : ∀ m : ℕ, bc57_pt (c + (m : ℤ)) 0 ∉ bc61_boxAround 2 L z) :
    Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
      (bc57_pt c 0) (bc57_pt (c + (j : ℤ)) 0) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt c 0)
  | succ i ih =>
    have hoff1 : bc57_pt (c + (i : ℤ) + 1) 0 ∉ bc61_boxAround 2 L z := by
      have := hoff (i + 1)
      rwa [show c + ((i + 1 : ℕ) : ℤ) = c + (i : ℤ) + 1 by push_cast; ring] at this
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
        (bc57_pt (c + (i : ℤ)) 0) (bc57_pt (c + (i : ℤ) + 1) 0) :=
      bc61_cut_adj_connected (bc57_pt_adj _ 0) (bcr_cross_horiz _) (hoff i) hoff1
    have hcast : c + ((i + 1 : ℕ) : ℤ) = c + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem brp_cross_vreach_up_avoid (L : ℕ) (z : Site 2) (hgt : ℤ) (j : ℕ)
    (hoff : ∀ m : ℕ, bc57_pt 0 (hgt + (m : ℤ)) ∉ bc61_boxAround 2 L z) :
    Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
      (bc57_pt 0 hgt) (bc57_pt 0 (hgt + (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 hgt)
  | succ i ih =>
    have hoff1 : bc57_pt 0 (hgt + (i : ℤ) + 1) ∉ bc61_boxAround 2 L z := by
      have := hoff (i + 1)
      rwa [show hgt + ((i + 1 : ℕ) : ℤ) = hgt + (i : ℤ) + 1 by push_cast; ring] at this
    have hstep : Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
        (bc57_pt 0 (hgt + (i : ℤ))) (bc57_pt 0 (hgt + (i : ℤ) + 1)) :=
      bc61_cut_adj_connected (bcr_vert_adj _) (bcr_cross_vert _) (hoff i) hoff1
    have hcast : hgt + ((i + 1 : ℕ) : ℤ) = hgt + (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans hstep


theorem brp_cross_vreach_down_avoid (L : ℕ) (z : Site 2) (hgt : ℤ) (j : ℕ)
    (hoff : ∀ m : ℕ, bc57_pt 0 (hgt - (m : ℤ)) ∉ bc61_boxAround 2 L z) :
    Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
      (bc57_pt 0 hgt) (bc57_pt 0 (hgt - (j : ℤ))) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 hgt)
  | succ i ih =>
    have hoff1 : bc57_pt 0 (hgt - (i : ℤ) - 1) ∉ bc61_boxAround 2 L z := by
      have := hoff (i + 1)
      rwa [show hgt - ((i + 1 : ℕ) : ℤ) = hgt - (i : ℤ) - 1 by push_cast; ring] at this
    have key : Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross)
        (bc57_pt 0 (hgt - (i : ℤ) - 1)) (bc57_pt 0 (hgt - (i : ℤ) - 1 + 1)) :=
      bc61_cut_adj_connected (bcr_vert_adj _) (bcr_cross_vert _) hoff1
        (by rw [show hgt - (i : ℤ) - 1 + 1 = hgt - (i : ℤ) by ring]; exact hoff i)
    have he : hgt - (i : ℤ) - 1 + 1 = hgt - (i : ℤ) := by ring
    rw [he] at key
    have hcast : hgt - ((i + 1 : ℕ) : ℤ) = hgt - (i : ℤ) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans key.symm


noncomputable def brp_witArm (R : ℕ) (i : Fin 3) : Site 2 :=
  if i = 0 then bc57_pt (R : ℤ) 0 else if i = 1 then bc57_pt 0 (R : ℤ) else bc57_pt 0 (-(R : ℤ))

@[simp] theorem brp_witArm_zero (R : ℕ) : brp_witArm R 0 = bc57_pt (R : ℤ) 0 := rfl
@[simp] theorem brp_witArm_one (R : ℕ) : brp_witArm R 1 = bc57_pt 0 (R : ℤ) := rfl
@[simp] theorem brp_witArm_two (R : ℕ) : brp_witArm R 2 = bc57_pt 0 (-(R : ℤ)) := rfl







theorem brp_cross_repRoute (L R : ℕ) (hR : L < R) :
    bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R) := by
  have hRz : (L : ℤ) < (R : ℤ) := by exact_mod_cast hR
  unfold bcr_RepRoute
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [brp_witArm_zero, brp_witArm_one, brp_witArm_two] at hij ⊢
  
  · exact absurd rfl hij
  
  · have h := brp_cross_hreach_avoid L (bc57_pt 0 (R : ℤ)) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_hreach_avoid L (bc57_pt 0 (-(R : ℤ))) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - -(R : ℤ) = (R : ℤ) by ring, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_vreach_up_avoid L (bc57_pt (R : ℤ) 0) 0 R (fun m => by
      refine brp_off_box_coord 0 ?_
      simp only [Pi.sub_apply, bc57_pt_fst]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_add] at h
    exact h
  
  · exact absurd rfl hij
  
  · have h := brp_cross_vreach_up_avoid L (bc57_pt 0 (-(R : ℤ))) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) + (m : ℤ) - -(R : ℤ) = (m : ℤ) + (R : ℤ) by ring]
      have : ((m : ℤ) + (R : ℤ)).natAbs = m + R := by
        rw [Int.natAbs_eq_iff]; left; push_cast; ring
      rw [this]; omega)
    rw [zero_add] at h
    exact h
  
  · have h := brp_cross_vreach_down_avoid L (bc57_pt (R : ℤ) 0) 0 R (fun m => by
      refine brp_off_box_coord 0 ?_
      simp only [Pi.sub_apply, bc57_pt_fst]
      rw [show (0 : ℤ) - (R : ℤ) = -(R : ℤ) by ring, Int.natAbs_neg, Int.natAbs_natCast]
      exact hR)
    rw [zero_sub] at h
    exact h
  
  · have h := brp_cross_vreach_down_avoid L (bc57_pt 0 (R : ℤ)) 0 R (fun m => by
      refine brp_off_box_coord 1 ?_
      simp only [Pi.sub_apply, bc57_pt_snd]
      rw [show (0 : ℤ) - (m : ℤ) - (R : ℤ) = -((m : ℤ) + (R : ℤ)) by ring, Int.natAbs_neg]
      have : ((m : ℤ) + (R : ℤ)).natAbs = m + R := by
        rw [Int.natAbs_eq_iff]; left; push_cast; ring
      rw [this]; omega)
    rw [zero_sub] at h
    exact h
  
  · exact absurd rfl hij





























theorem brp_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x : Site d) (a : Fin 3 → Site d),
      x ∈ box d R → bc67_IsGnTrifurcation ω L x →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) →
      (∀ i, a i ∈ vertexBoundary d R) → (∀ i, a i ≠ x) → Function.Injective a →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j)) →
      bcr_RepRoute ω L x a → bgc_TrifForestData ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d) (tip b : Fin 3 → Site d),
      (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i)) →
      (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) →
      bcr_RepRoute ω L x tip) ∧
    
    (∀ (L R : ℕ), L < R → bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R x a hxbox hxtri hsingle habdry hxne hainj hsep hroute
    exact brp_trifForestData_of_repRoute ω L R a hxbox hxtri hsingle habdry hxne hainj hsep hroute
  · intro ω L x tip b hentry htail; exact brp_repRoute_of_entry ω L x tip b hentry htail
  · intro L R hR; exact brp_cross_repRoute L R hR

end StatMech.Walls
