/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Walls.bfkforestbuild

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation






variable {d : ℕ}



theorem btr_removed_isolated {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (ha : a ∈ T) (hconn : Connected d (removeSites T ω) a b) : b = a := by
  obtain ⟨w⟩ := hconn
  cases w with
  | nil => rfl
  | cons hadj w' =>
      exfalso
      rw [openSubgraph_adj] at hadj
      obtain ⟨_, hopen⟩ := hadj
      unfold removeSites at hopen
      rw [if_pos ⟨a, ha, Sym2.mem_mk_left a _⟩] at hopen
      exact Bool.false_ne_true hopen




theorem btr_arm_outside_box {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))} {a : Site d}
    (hinf : (cluster d (removeSites T ω) a).Infinite) : a ∉ T := by
  intro ha
  have hsub : cluster d (removeSites T ω) a ⊆ {a} := by
    intro b hb
    rw [mem_cluster] at hb
    rw [Set.mem_singleton_iff]
    exact btr_removed_isolated ha hb
  exact hinf (Set.Finite.subset (Set.finite_singleton a) hsub)














def btr_IsGenuineCoarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (∃ b₁ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₁ a₁) ∧
    (∃ b₂ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₂ a₂) ∧
    (∃ b₃ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₃ a₃) ∧
    
    (Connected d ω y a₁ ∧ Connected d ω y a₂ ∧ Connected d ω y a₃) ∧
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃)




theorem btr_genuine_imp_bc61 {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y : Site d}
    (h : btr_IsGenuineCoarseTrif ω L y) : bc61_IsCoarseTrifurcation ω L y := by
  obtain ⟨a₁, a₂, a₃, hb1, hb2, hb3, _hcy, hinf, hsep⟩ := h
  exact ⟨a₁, a₂, a₃, hb1, hb2, hb3, hinf, hsep⟩










theorem btr_pt_outside {L : ℕ} {m h₀ c H : ℤ} (hc : L < (c - m).natAbs) :
    bc57_pt c H ∉ bc61_boxAround 2 L (bc57_pt m h₀) := by
  rw [bc61_mem_boxAround, mem_box]
  simp only [not_forall, not_le]
  refine ⟨0, ?_⟩
  simp only [Pi.sub_apply, bc57_pt_fst]
  omega


theorem btr_right_reach {L : ℕ} {m h₀ h c : ℤ} (hh : 1 ≤ h) (hc : (L : ℤ) < c - m) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt c h) (bc57_pt (c + (j : ℤ)) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt c h)
  | succ i ih =>
      have hstep : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
          (bc57_pt (c + (i : ℤ)) h) (bc57_pt (c + (i : ℤ) + 1) h) :=
        bc61_cut_adj_connected (bc57_pt_adj _ h) (bc60_open _ hh)
          (btr_pt_outside (m := m) (h₀ := h₀) (c := c + (i : ℤ)) (H := h) (by omega))
          (btr_pt_outside (m := m) (h₀ := h₀) (c := c + (i : ℤ) + 1) (H := h) (by omega))
      have hcast : c + ((i + 1 : ℕ) : ℤ) = c + (i : ℤ) + 1 := by push_cast; ring
      rw [hcast]; exact ih.trans hstep


theorem btr_left_reach {L : ℕ} {m h₀ h c : ℤ} (hh : 1 ≤ h) (hc : c - m < -(L : ℤ)) (j : ℕ) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt c h) (bc57_pt (c - (j : ℤ)) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt c h)
  | succ i ih =>
      have key : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
          (bc57_pt (c - (i : ℤ) - 1) h) (bc57_pt (c - (i : ℤ) - 1 + 1) h) :=
        bc61_cut_adj_connected (bc57_pt_adj (c - (i : ℤ) - 1) h)
          (bc60_open (c - (i : ℤ) - 1) hh)
          (btr_pt_outside (m := m) (h₀ := h₀) (c := c - (i : ℤ) - 1) (H := h) (by omega))
          (btr_pt_outside (m := m) (h₀ := h₀) (c := c - (i : ℤ) - 1 + 1) (H := h) (by omega))
      have he : c - (i : ℤ) - 1 + 1 = c - (i : ℤ) := by ring
      rw [he] at key
      have hcast : c - ((i + 1 : ℕ) : ℤ) = c - (i : ℤ) - 1 := by push_cast; ring
      rw [hcast]; exact ih.trans key.symm


theorem btr_sameSide_right {L : ℕ} {m h₀ h c c' : ℤ} (hh : 1 ≤ h)
    (hc : (L : ℤ) < c - m) (hc' : (L : ℤ) < c' - m) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt c h) (bc57_pt c' h) := by
  rcases le_total c c' with hle | hle
  · have hr := btr_right_reach (m := m) (h₀ := h₀) hh hc (c' - c).toNat
    have hcast : c + ((c' - c).toNat : ℤ) = c' := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rwa [hcast] at hr
  · have hr := btr_right_reach (m := m) (h₀ := h₀) hh hc' (c - c').toNat
    have hcast : c' + ((c - c').toNat : ℤ) = c := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hcast] at hr; exact hr.symm


theorem btr_sameSide_left {L : ℕ} {m h₀ h c c' : ℤ} (hh : 1 ≤ h)
    (hc : c - m < -(L : ℤ)) (hc' : c' - m < -(L : ℤ)) :
    Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines)
      (bc57_pt c h) (bc57_pt c' h) := by
  rcases le_total c' c with hle | hle
  · have hr := btr_left_reach (m := m) (h₀ := h₀) hh hc (c - c').toNat
    have hcast : c - ((c - c').toNat : ℤ) = c' := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rwa [hcast] at hr
  · have hr := btr_left_reach (m := m) (h₀ := h₀) hh hc' (c' - c).toNat
    have hcast : c' - ((c' - c).toNat : ℤ) = c := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hcast] at hr; exact hr.symm




theorem btr_site_eq (x : Site 2) : x = bc57_pt (x 0) (x 1) := by
  funext i; fin_cases i <;> simp [bc57_pt]


theorem btr_center_mem_box {L : ℕ} (y : Site 2) : y ∈ bc61_boxAround 2 L y := by
  rw [bc61_mem_boxAround, mem_box]
  intro i
  simp only [sub_self, Pi.zero_apply, Int.natAbs_zero]
  exact Nat.zero_le L



theorem btr_height_pos {u v : Site 2} (hne : v ≠ u) (hconn : Connected 2 bc60_upperLines u v) :
    1 ≤ u 1 := by
  obtain ⟨w⟩ := hconn
  cases w with
  | nil => exact absurd rfl hne
  | cons hadj w' =>
      rw [openSubgraph_adj] at hadj
      exact (bc60_open_edge_heights hadj.2).1


theorem btr_outside_col {L : ℕ} {m h₀ c : ℤ}
    (hout : bc57_pt c h₀ ∉ bc61_boxAround 2 L (bc57_pt m h₀)) :
    L < (c - m).natAbs := by
  rw [bc61_mem_boxAround, mem_box] at hout
  simp only [not_forall, not_le] at hout
  obtain ⟨i, hi⟩ := hout
  fin_cases i
  · have hi' : L < ((bc57_pt c h₀ - bc57_pt m h₀) (0 : Fin 2)).natAbs := hi
    simpa [Pi.sub_apply, bc57_pt_fst] using hi'
  · exfalso
    have hi' : L < ((bc57_pt c h₀ - bc57_pt m h₀) (1 : Fin 2)).natAbs := hi
    simp only [Pi.sub_apply, bc57_pt_snd, sub_self, Int.natAbs_zero] at hi'
    omega









theorem btr_bc60_not_genuineTrif (L : ℕ) (y : Site 2) :
    ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y := by
  rintro ⟨a₁, a₂, a₃, _hb1, _hb2, _hb3, ⟨hcy1, hcy2, hcy3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
  have hyeq : y = bc57_pt (y 0) (y 1) := btr_site_eq y
  
  have ho1 : a₁ ∉ bc61_boxAround 2 L y := btr_arm_outside_box hi1
  have ho2 : a₂ ∉ bc61_boxAround 2 L y := btr_arm_outside_box hi2
  have ho3 : a₃ ∉ bc61_boxAround 2 L y := btr_arm_outside_box hi3
  
  have hyb : y ∈ bc61_boxAround 2 L y := btr_center_mem_box y
  have hne1 : a₁ ≠ y := fun h => ho1 (h ▸ hyb)
  have hhpos : 1 ≤ y 1 := btr_height_pos (u := y) (v := a₁) hne1 hcy1
  
  have hht1 : a₁ 1 = y 1 := bc60_height_invariant (u := y) rfl hcy1
  have hht2 : a₂ 1 = y 1 := bc60_height_invariant (u := y) rfl hcy2
  have hht3 : a₃ 1 = y 1 := bc60_height_invariant (u := y) rfl hcy3
  have hae1 : a₁ = bc57_pt (a₁ 0) (y 1) := by rw [← hht1]; exact btr_site_eq a₁
  have hae2 : a₂ = bc57_pt (a₂ 0) (y 1) := by rw [← hht2]; exact btr_site_eq a₂
  have hae3 : a₃ = bc57_pt (a₃ 0) (y 1) := by rw [← hht3]; exact btr_site_eq a₃
  
  have hc1 : L < (a₁ 0 - y 0).natAbs :=
    btr_outside_col (m := y 0) (h₀ := y 1) (c := a₁ 0) (by rw [← hae1, ← hyeq]; exact ho1)
  have hc2 : L < (a₂ 0 - y 0).natAbs :=
    btr_outside_col (m := y 0) (h₀ := y 1) (c := a₂ 0) (by rw [← hae2, ← hyeq]; exact ho2)
  have hc3 : L < (a₃ 0 - y 0).natAbs :=
    btr_outside_col (m := y 0) (h₀ := y 1) (c := a₃ 0) (by rw [← hae3, ← hyeq]; exact ho3)
  
  have hside1 : (L : ℤ) < a₁ 0 - y 0 ∨ a₁ 0 - y 0 < -(L : ℤ) := by omega
  have hside2 : (L : ℤ) < a₂ 0 - y 0 ∨ a₂ 0 - y 0 < -(L : ℤ) := by omega
  have hside3 : (L : ℤ) < a₃ 0 - y 0 ∨ a₃ 0 - y 0 < -(L : ℤ) := by omega
  
  rcases hside1 with hR1 | hL1 <;> rcases hside2 with hR2 | hL2 <;> rcases hside3 with hR3 | hL3
  · exact hs12 (by rw [hae1, hae2, hyeq]; exact btr_sameSide_right hhpos hR1 hR2)
  · exact hs12 (by rw [hae1, hae2, hyeq]; exact btr_sameSide_right hhpos hR1 hR2)
  · exact hs13 (by rw [hae1, hae3, hyeq]; exact btr_sameSide_right hhpos hR1 hR3)
  · exact hs23 (by rw [hae2, hae3, hyeq]; exact btr_sameSide_left hhpos hL2 hL3)
  · exact hs23 (by rw [hae2, hae3, hyeq]; exact btr_sameSide_right hhpos hR2 hR3)
  · exact hs13 (by rw [hae1, hae3, hyeq]; exact btr_sameSide_left hhpos hL1 hL3)
  · exact hs12 (by rw [hae1, hae2, hyeq]; exact btr_sameSide_left hhpos hL1 hL2)
  · exact hs12 (by rw [hae1, hae2, hyeq]; exact btr_sameSide_left hhpos hL1 hL2)




noncomputable def btr_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (boxFinsetBK d R).filter (fun y => btr_IsGenuineCoarseTrif ω L y)




theorem btr_bc60_genuineTrifFinset_empty (L R : ℕ) :
    btr_genuineTrifFinset bc60_upperLines L R = ∅ := by
  classical
  rw [btr_genuineTrifFinset, Finset.filter_eq_empty_iff]
  intro y _
  exact btr_bc60_not_genuineTrif L y


theorem btr_bc60_genuineTcount_zero (L R : ℕ) :
    (btr_genuineTrifFinset bc60_upperLines L R).card = 0 := by
  rw [btr_bc60_genuineTrifFinset_empty]; simp

























theorem btr_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
      btr_IsGenuineCoarseTrif ω L y → bc61_IsCoarseTrifurcation ω L y) ∧
    
    (∀ (L : ℕ) (y : Site 2), ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y) ∧
    
    (∀ (L R : ℕ), (btr_genuineTrifFinset bc60_upperLines L R).card = 0) :=
  ⟨fun ω L y h => btr_genuine_imp_bc61 h,
   fun L y => btr_bc60_not_genuineTrif L y,
   fun L R => btr_bc60_genuineTcount_zero L R⟩

end StatMech.Walls
