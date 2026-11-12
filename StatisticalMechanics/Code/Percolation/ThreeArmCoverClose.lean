/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.ForestSelectorProve
import Code.Percolation.ForestColouringClose2
import Code.Percolation.BKHallSDRClose
import Code.Percolation.ArmEndDisjointClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem tac_not_threeArmCover_of_fourArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {y : Site d} (hybox : y ∈ box d n) (htri : IsTrifurcation d ω y)
    (c : Fin 4 → Site d)
    (hconn : ∀ k, Connected d ω y (c k)) (hne : ∀ k, y ≠ c k)
    (hdis : ∀ k l, k ≠ l → ¬ Connected d (removeSite y ω) (c k) (c l)) :
    ¬ fcc_ThreeArmCover ω n := by
  classical
  rintro ⟨arms, harms⟩
  obtain ⟨hsep, hcover⟩ := harms y hybox htri
  
  choose i hi using fun k => hcover (c k) (hconn k) (hne k)
  
  obtain ⟨k, l, hkl, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
  
  have hwit_kl : Connected d (removeSite y ω)
      (fsp_armWitness ω y (c k)) (fsp_armWitness ω y (c l)) := by
    have h1 := hi k
    have h2 := hi l
    rw [hcol] at h1
    exact h1.symm.trans h2
  
  have hck : Connected d (removeSite y ω) (fsp_armWitness ω y (c k)) (c k) :=
    fsp_armWitness_inArm ω (hconn k) (hne k)
  have hcl : Connected d (removeSite y ω) (fsp_armWitness ω y (c l)) (c l) :=
    fsp_armWitness_inArm ω (hconn l) (hne l)
  exact hdis k l hkl (hck.symm.trans (hwit_kl.trans hcl))










noncomputable def tac_plus : ConfigSpace (Sym2 (Site 2)) :=
  fun e => Sym2.lift ⟨fun x y => (decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0)),
    by
      intro x y
      simp only [Bool.or_comm]
      congr 1 <;> · rw [decide_eq_decide]; tauto⟩ e

@[simp] theorem tac_plus_mk (x y : Site 2) :
    tac_plus s(x, y) = ((decide (x 1 = 0 ∧ y 1 = 0)) || (decide (x 0 = 0 ∧ y 0 = 0))) := rfl


theorem tac_isOpenEdge_iff (x y : Site 2) :
    IsOpenEdge 2 tac_plus x y ↔
      (hypercubicLattice 2).Adj x y ∧ ((x 1 = 0 ∧ y 1 = 0) ∨ (x 0 = 0 ∧ y 0 = 0)) := by
  unfold IsOpenEdge
  rw [tac_plus_mk]
  simp [Bool.or_eq_true, decide_eq_true_eq]




def tac_ray (x : Site 2) : ℤ :=
  if x 1 = 0 ∧ 1 ≤ x 0 then 1
  else if x 1 = 0 ∧ x 0 ≤ -1 then 2
  else if x 0 = 0 ∧ 1 ≤ x 1 then 3
  else if x 0 = 0 ∧ x 1 ≤ -1 then 4
  else 0

theorem tac_ray_east : tac_ray ![1, 0] = 1 := by simp [tac_ray]
theorem tac_ray_west : tac_ray ![-1, 0] = 2 := by simp [tac_ray]
theorem tac_ray_north : tac_ray ![0, 1] = 3 := by simp [tac_ray]
theorem tac_ray_south : tac_ray ![0, -1] = 4 := by simp [tac_ray]




theorem tac_ray_invariant {x y : Site 2}
    (h : IsOpenEdge 2 (removeSite (0 : Site 2) tac_plus) x y) :
    tac_ray x = tac_ray y := by
  obtain ⟨hadj, hopen⟩ := h
  have h0 : (0 : Site 2) ∉ s(x, y) := by
    by_contra hc
    rw [removeSite_apply_of_mem hc] at hopen
    exact absurd hopen (by simp)
  have hxne : x ≠ (0 : Site 2) := fun h => h0 (h ▸ Sym2.mem_mk_left _ _)
  have hyne : y ≠ (0 : Site 2) := fun h => h0 (h ▸ Sym2.mem_mk_right _ _)
  rw [removeSite_apply_of_notMem h0] at hopen
  have hplus : IsOpenEdge 2 tac_plus x y := ⟨hadj, hopen⟩
  rw [tac_isOpenEdge_iff] at hplus
  obtain ⟨hadj', hcase⟩ := hplus
  have hadjsum : (∑ i, (x i - y i).natAbs) = 1 := hadj'
  rw [Fin.sum_univ_two] at hadjsum
  have hx0ne : x ≠ ![0, 0] := by
    rwa [show (0 : Site 2) = ![0, 0] by funext i; fin_cases i <;> simp] at hxne
  have hy0ne : y ≠ ![0, 0] := by
    rwa [show (0 : Site 2) = ![0, 0] by funext i; fin_cases i <;> simp] at hyne
  rcases hcase with ⟨hx1, hy1⟩ | ⟨hx0, hy0⟩
  · 
    have hx0z : x 0 ≠ 0 := fun hc => hx0ne (by funext i; fin_cases i <;> simp_all)
    have hy0z : y 0 ≠ 0 := fun hc => hy0ne (by funext i; fin_cases i <;> simp_all)
    have hsub1 : (x 1 - y 1).natAbs = 0 := by rw [hx1, hy1]; simp
    rw [hsub1, add_zero] at hadjsum
    have hd : (x 0 - y 0).natAbs = 1 := hadjsum
    have hsame : (1 ≤ x 0 ∧ 1 ≤ y 0) ∨ (x 0 ≤ -1 ∧ y 0 ≤ -1) := by omega
    rcases hsame with ⟨hxe, hye⟩ | ⟨hxw, hyw⟩
    · rw [tac_ray, tac_ray, if_pos ⟨hx1, hxe⟩, if_pos ⟨hy1, hye⟩]
    · rw [tac_ray, tac_ray]
      rw [if_neg (by omega), if_pos ⟨hx1, hxw⟩, if_neg (by omega), if_pos ⟨hy1, hyw⟩]
  · 
    have hx1z : x 1 ≠ 0 := fun hc => hx0ne (by funext i; fin_cases i <;> simp_all)
    have hy1z : y 1 ≠ 0 := fun hc => hy0ne (by funext i; fin_cases i <;> simp_all)
    have hsub0 : (x 0 - y 0).natAbs = 0 := by rw [hx0, hy0]; simp
    rw [hsub0, zero_add] at hadjsum
    have hd : (x 1 - y 1).natAbs = 1 := hadjsum
    have hsame : (1 ≤ x 1 ∧ 1 ≤ y 1) ∨ (x 1 ≤ -1 ∧ y 1 ≤ -1) := by omega
    rcases hsame with ⟨hxn, hyn⟩ | ⟨hxs, hys⟩
    · rw [tac_ray, tac_ray]
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hx0, hxn⟩,
        if_neg (by omega), if_neg (by omega), if_pos ⟨hy0, hyn⟩]
    · rw [tac_ray, tac_ray]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hx0, hxs⟩,
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hy0, hys⟩]


theorem tac_ray_const_of_connected {x y : Site 2}
    (h : Connected 2 (removeSite (0 : Site 2) tac_plus) x y) :
    tac_ray x = tac_ray y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (tac_ray_invariant hadj).trans ih


theorem tac_disconnected_of_ne_ray {x y : Site 2} (h : tac_ray x ≠ tac_ray y) :
    ¬ Connected 2 (removeSite (0 : Site 2) tac_plus) x y :=
  fun hc => h (tac_ray_const_of_connected hc)




theorem tac_conn_east (k : ℕ) : Connected 2 tac_plus ![1, 0] ![(k : ℤ) + 1, 0] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(1:ℤ), 0]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![(m:ℤ)+1, 0] ![((m:ℤ)+1)+1, 0] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inl ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (((m : ℤ) + 1) + 1) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at h


theorem tac_conn_west (k : ℕ) : Connected 2 tac_plus ![-1, 0] ![-((k : ℤ) + 1), 0] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(-1:ℤ), 0]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![-((m:ℤ)+1), 0] ![-(((m:ℤ)+1)+1), 0] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inl ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (-(((m : ℤ) + 1) + 1)) = -(((m + 1 : ℕ) : ℤ) + 1) by push_cast; ring] at h


theorem tac_conn_north (k : ℕ) : Connected 2 tac_plus ![0, 1] ![0, (k : ℤ) + 1] := by
  induction k with
  | zero => simpa using connected_refl tac_plus ![(0:ℤ), 1]
  | succ m ih =>
    refine ih.trans ?_
    have hstep : IsOpenEdge 2 tac_plus ![0, (m:ℤ)+1] ![0, ((m:ℤ)+1)+1] := by
      rw [tac_isOpenEdge_iff]
      exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
        Or.inr ⟨by simp, by simp⟩⟩
    have h := hstep.connected
    rwa [show (((m : ℤ) + 1) + 1) = ((m + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at h


theorem tac_east_infinite : (cluster 2 tac_plus ![1, 0]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![(k : ℤ) + 1, 0] : Site 2)) ?_ ?_
  · intro a b hab; have : (a : ℤ) + 1 = (b : ℤ) + 1 := congrFun hab 0; omega
  · intro k; exact tac_conn_east k


theorem tac_west_infinite : (cluster 2 tac_plus ![-1, 0]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![-((k : ℤ) + 1), 0] : Site 2)) ?_ ?_
  · intro a b hab; have : -((a : ℤ) + 1) = -((b : ℤ) + 1) := congrFun hab 0; omega
  · intro k; exact tac_conn_west k


theorem tac_north_infinite : (cluster 2 tac_plus ![0, 1]).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (![0, (k : ℤ) + 1] : Site 2)) ?_ ?_
  · intro a b hab; have : (a : ℤ) + 1 = (b : ℤ) + 1 := congrFun hab 1; omega
  · intro k; exact tac_conn_north k


theorem tac_origin_east : Connected 2 tac_plus (0 : Site 2) ![1, 0] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inl ⟨by simp, by simp⟩⟩)

theorem tac_origin_west : Connected 2 tac_plus (0 : Site 2) ![-1, 0] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inl ⟨by simp, by simp⟩⟩)

theorem tac_origin_north : Connected 2 tac_plus (0 : Site 2) ![0, 1] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inr ⟨by simp, by simp⟩⟩)

theorem tac_origin_south : Connected 2 tac_plus (0 : Site 2) ![0, -1] :=
  IsOpenEdge.connected (by
    rw [tac_isOpenEdge_iff]
    exact ⟨by simp only [hypercubicLattice_adj]; rw [Fin.sum_univ_two]; simp,
      Or.inr ⟨by simp, by simp⟩⟩)






theorem tac_origin_isTrifurcation : IsTrifurcation 2 tac_plus (0 : Site 2) := by
  refine ⟨![1, 0], ![-1, 0], ![0, 1], ⟨by decide, by decide, by decide⟩,
    ⟨tac_origin_east, tac_origin_west, tac_origin_north⟩,
    ⟨tac_east_infinite, tac_west_infinite, tac_north_infinite⟩, ?_, ?_, ?_⟩
  · exact tac_disconnected_of_ne_ray (by decide)
  · exact tac_disconnected_of_ne_ray (by decide)
  · exact tac_disconnected_of_ne_ray (by decide)








theorem tac_threeArmCover_false : ¬ fcc_ThreeArmCover (d := 2) tac_plus 1 := by
  refine tac_not_threeArmCover_of_fourArm tac_plus 1 (y := (0 : Site 2)) ?_
    tac_origin_isTrifurcation ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]] ?_ ?_ ?_
  · 
    intro i; simp
  · 
    intro k; fin_cases k
    · exact tac_origin_east
    · exact tac_origin_west
    · exact tac_origin_north
    · exact tac_origin_south
  · 
    intro k; fin_cases k <;> exact (by decide)
  · 
    intro k l hkl
    fin_cases k <;> fin_cases l <;>
      first
      | exact absurd rfl hkl
      | exact tac_disconnected_of_ne_ray (by decide)













theorem tac_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn h





theorem tac_burton_keane_bernoulli_of_globalForestArms (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  aed_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0 hres htrif

end Percolation

end StatMech
