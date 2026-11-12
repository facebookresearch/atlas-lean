/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.MultiReplica
import Code.Ising.AizenmanSignDominance

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

namespace AizenmanDecomp

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]











theorem aid_conn_trans_xy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hoy : connK ends m o y) (hox : connK ends m o x) : connK ends m x y :=
  Relation.ReflTransGen.trans (connK_symm ends m hox) hoy



theorem aid_conn_trans_ox (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hoy : connK ends m o y) : connK ends m o x :=
  Relation.ReflTransGen.trans hoy (connK_symm ends m hxy)



theorem aid_conn_trans_oy (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hxy : connK ends m x y) (hox : connK ends m o x) : connK ends m o y :=
  Relation.ReflTransGen.trans hox hxy


def aid_allConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  connK ends m x y ∧ connK ends m o y ∧ connK ends m o x


def aid_noneConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) : Prop :=
  ¬ connK ends m x y ∧ ¬ connK ends m o y ∧ ¬ connK ends m o x


theorem aid_noneConn_not_allConn (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aid_noneConn ends m o x y) : ¬ aid_allConn ends m o x y := by
  rintro ⟨h1, _, _⟩; exact h.1 h1






theorem aid_backbone_trichotomy (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    asd_ghsBackboneFactor ends m o x y = 1
    ∨ asd_ghsBackboneFactor ends m o x y = 0
    ∨ asd_ghsBackboneFactor ends m o x y = -2 := by
  unfold asd_ghsBackboneFactor
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · right; right; rw [if_pos hxy, if_pos hoy, if_pos hox]; norm_num
  · exact absurd (aid_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aid_conn_trans_oy ends m hxy hox) hoy
  · right; left; rw [if_pos hxy, if_neg hoy, if_neg hox]; norm_num
  · exact absurd (aid_conn_trans_xy ends m hoy hox) hxy
  · right; left; rw [if_neg hxy, if_pos hoy, if_neg hox]; norm_num
  · right; left; rw [if_neg hxy, if_neg hoy, if_pos hox]; norm_num
  · left; rw [if_neg hxy, if_neg hoy, if_neg hox]; norm_num


theorem aid_backbone_value_none (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aid_noneConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = 1 :=
  asd_ghsBackboneFactor_noConn ends m h.1 h.2.1 h.2.2


theorem aid_backbone_value_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (h : aid_allConn ends m o x y) : asd_ghsBackboneFactor ends m o x y = -2 :=
  asd_ghsBackboneFactor_allConn ends m h.1 h.2.1 h.2.2




theorem aid_backbone_value_one (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aid_allConn ends m o x y) (hnotnone : ¬ aid_noneConn ends m o x y) :
    asd_ghsBackboneFactor ends m o x y = 0 := by
  unfold asd_ghsBackboneFactor
  simp only [aid_allConn, aid_noneConn] at hnotall hnotnone
  by_cases hxy : connK ends m x y <;> by_cases hoy : connK ends m o y <;>
    by_cases hox : connK ends m o x
  · exact absurd ⟨hxy, hoy, hox⟩ hnotall
  · exact absurd (aid_conn_trans_ox ends m hxy hoy) hox
  · exact absurd (aid_conn_trans_oy ends m hxy hox) hoy
  · rw [if_pos hxy, if_neg hoy, if_neg hox]; norm_num
  · exact absurd (aid_conn_trans_xy ends m hoy hox) hxy
  · rw [if_neg hxy, if_pos hoy, if_neg hox]; norm_num
  · rw [if_neg hxy, if_neg hoy, if_pos hox]; norm_num
  · exact absurd ⟨hxy, hoy, hox⟩ hnotnone




theorem aid_backbone_factor_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hnotall : ¬ aid_allConn ends m o x y) : 0 ≤ asd_ghsBackboneFactor ends m o x y := by
  by_cases hnone : aid_noneConn ends m o x y
  · rw [aid_backbone_value_none ends m hnone]; norm_num
  · rw [aid_backbone_value_one ends m hnotall hnone]





noncomputable def aid_mass (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (S : Finset V) :
    ℝ :=
  ∑ K ∈ m.powerset.filter (fun K => Sharpness.RandomCurrent.sources ends K = S), φ K



noncomputable def aid_gap (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ) (A : Finset V)
    (o x y : V) : ℝ :=
  aid_mass ends m φ A - aid_mass ends m φ (A ∆ {x, y})
    - aid_mass ends m φ (A ∆ {o, y}) - aid_mass ends m φ (A ∆ {o, x})


theorem aid_mass_nonneg (ends : ι → Sym2 V) (m : Finset ι) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (S : Finset V) : 0 ≤ aid_mass ends m φ S :=
  Finset.sum_nonneg (fun K _ => hφnn K)





theorem aid_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aid_gap ends m φ A o x y = aid_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
  unfold aid_gap aid_mass asd_ghsBackboneFactor
  exact asd_ghsSigned_eq ends m hnd A hm hox hoy hxy φ hφ




theorem aid_per_super_nonneg_not_all (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aid_allConn ends m o x y) :
    0 ≤ aid_gap ends m φ A o x y := by
  rw [aid_gap_eq ends m hnd A hm hox hoy hxy φ hφ]
  exact mul_nonneg (aid_mass_nonneg ends m φ hφnn A)
    (aid_backbone_factor_nonneg_not_all ends m hnotall)




theorem aid_gap_allConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) (hall : aid_allConn ends m o x y) :
    aid_gap ends m φ A o x y = -2 * aid_mass ends m φ A := by
  rw [aid_gap_eq ends m hnd A hm hox hoy hxy φ hφ, aid_backbone_value_all ends m hall]; ring




theorem aid_gap_noneConn (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) (hnone : aid_noneConn ends m o x y) :
    aid_gap ends m φ A o x y = aid_mass ends m φ A := by
  rw [aid_gap_eq ends m hnd A hm hox hoy hxy φ hφ, aid_backbone_value_none ends m hnone]; ring



theorem aid_gap_exactlyOne (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hnotall : ¬ aid_allConn ends m o x y) (hnotnone : ¬ aid_noneConn ends m o x y) :
    aid_gap ends m φ A o x y = 0 := by
  rw [aid_gap_eq ends m hnd A hm hox hoy hxy φ hφ,
      aid_backbone_value_one ends m hnotall hnotnone]; ring









theorem aid_inclusion_exclusion_split (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) (o x y : V) (Φ : Finset ι → Finset ι → ℝ) :
    ∑ m ∈ M, aid_gap ends m (Φ m) A o x y
      = (∑ m ∈ M, aid_mass ends m (Φ m) A)
        - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {x, y}))
        - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, y}))
        - (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, x})) := by
  unfold aid_gap
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]









theorem aid_decomp_allConn_sum (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_gap ends m (Φ m) A o x y
      = -2 * ∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hmem => ?_)
  rw [Finset.mem_filter] at hmem
  exact aid_gap_allConn ends m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy (Φ m)
    (hΦ m hmem.1) hmem.2






theorem aid_decomp_notAllConn_sum (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M.filter (fun m => ¬ aid_allConn ends m o x y), aid_gap ends m (Φ m) A o x y
      = ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A := by
  rw [← Finset.sum_filter_add_sum_filter_not (M.filter (fun m => ¬ aid_allConn ends m o x y))
    (fun m => aid_noneConn ends m o x y) (fun m => aid_gap ends m (Φ m) A o x y)]
  
  have hfilt : (M.filter (fun m => ¬ aid_allConn ends m o x y)).filter
      (fun m => aid_noneConn ends m o x y) = M.filter (fun m => aid_noneConn ends m o x y) := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm0, _⟩, hn⟩; exact ⟨hm0, hn⟩
    · rintro ⟨hm0, hn⟩
      exact ⟨⟨hm0, aid_noneConn_not_allConn ends m hn⟩, hn⟩
  
  have h1 : ∑ m ∈ (M.filter (fun m => ¬ aid_allConn ends m o x y)).filter
        (fun m => aid_noneConn ends m o x y), aid_gap ends m (Φ m) A o x y
      = ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A := by
    rw [hfilt]
    refine Finset.sum_congr rfl (fun m hmem => ?_)
    rw [Finset.mem_filter] at hmem
    exact aid_gap_noneConn ends m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy (Φ m)
      (hΦ m hmem.1) hmem.2
  
  have h2 : ∑ m ∈ (M.filter (fun m => ¬ aid_allConn ends m o x y)).filter
        (fun m => ¬ aid_noneConn ends m o x y), aid_gap ends m (Φ m) A o x y = 0 := by
    refine Finset.sum_eq_zero (fun m hmem => ?_)
    simp only [Finset.mem_filter] at hmem
    exact aid_gap_exactlyOne ends m (hnd m hmem.1.1) A (hm m hmem.1.1) hox hoy hxy (Φ m)
      (hΦ m hmem.1.1) hmem.1.2 hmem.2
  rw [h1, h2, add_zero]













theorem aid_inclusion_exclusion_decomp (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M, aid_gap ends m (Φ m) A o x y
      = (∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A)
        - 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A) := by
  
  rw [← Finset.sum_filter_add_sum_filter_not M (fun m => aid_allConn ends m o x y)
    (fun m => aid_gap ends m (Φ m) A o x y),
    aid_decomp_allConn_sum ends M hnd A hm hox hoy hxy Φ hΦ,
    aid_decomp_notAllConn_sum ends M hnd A hm hox hoy hxy Φ hΦ]
  ring






















theorem aid_inclusion_exclusion (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A) :
    0 ≤ ∑ m ∈ M, aid_gap ends m (Φ m) A o x y := by
  rw [aid_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ]
  linarith









theorem aid_ghs_distinct_site (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.RandomCurrent.sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => aid_allConn ends m o x y), aid_mass ends m (Φ m) A)
      ≤ ∑ m ∈ M.filter (fun m => aid_noneConn ends m o x y), aid_mass ends m (Φ m) A) :
    (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {x, y}))
      + (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, y}))
      + (∑ m ∈ M, aid_mass ends m (Φ m) (A ∆ {o, x}))
      ≤ ∑ m ∈ M, aid_mass ends m (Φ m) A := by
  have hge : 0 ≤ ∑ m ∈ M, aid_gap ends m (Φ m) A o x y :=
    aid_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom
  rw [aid_inclusion_exclusion_split ends M A o x y Φ] at hge
  linarith

end AizenmanDecomp

end Ising

end StatMech
