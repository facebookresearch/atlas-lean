/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Mathlib
import Code.Ising.TwoReplica
import Code.Ising.TwoReplicaWeighted
import Code.Ising.BackboneExists
import Code.Sharpness.RandomCurrent
import Code.Sharpness.TwoReplica
import Code.Ising.AizenmanSignDominance

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]













noncomputable def hnw_mass (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (S : Finset V) : ℝ :=
  splitWeightedSum G β J m 1 S




noncomputable def hnw_gap (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    (o x y : V) : ℝ :=
  hnw_mass G β J m A - hnw_mass G β J m (A ∆ {x, y})
    - hnw_mass G β J m (A ∆ {o, y}) - hnw_mass G β J m (A ∆ {o, x})



theorem hnw_mass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (S : Finset V) : 0 ≤ hnw_mass G β J m S :=
  asd_splitWeightedSum_nonneg G β J hβ hJ m 1 (by norm_num) S







def hnw_allConn (m : Current V) (o x y : V) : Prop :=
  connP (oddEdges G.edgeFinset m) x y ∧ connP (oddEdges G.edgeFinset m) o y
    ∧ connP (oddEdges G.edgeFinset m) o x




def hnw_noneConn (m : Current V) (o x y : V) : Prop :=
  ¬ connP (posEdges G.edgeFinset m) x y ∧ ¬ connP (posEdges G.edgeFinset m) o y
    ∧ ¬ connP (posEdges G.edgeFinset m) o x




theorem hnw_noneConn_not_allConn (m : Current V) {o x y : V}
    (h : hnw_noneConn G m o x y) : ¬ hnw_allConn G m o x y := by
  rintro ⟨hxy, _, _⟩
  exact h.1 (connOdd_imp_connPos G.edgeFinset m hxy)












theorem hnw_switching (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges G.edgeFinset m) u v) (A : Finset V) :
    hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A :=
  ising_switching_weighted G β J m huv hconn 1 A










theorem hnw_mass_vanish (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {u v : V} (huv : u ≠ v) (hdisc : ¬ connP (posEdges G.edgeFinset m) u v) :
    hnw_mass G β J m (A ∆ {u, v}) = 0 :=
  ising_switching_weighted_vanishing G β J m hnd A hm huv hdisc 1




theorem hnw_conn_trans_xy (m : Current V) {o x y : V}
    (hoy : connP (oddEdges G.edgeFinset m) o y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) x y :=
  Relation.ReflTransGen.trans (connP_symm _ hox) hoy


theorem hnw_conn_trans_ox (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hoy : connP (oddEdges G.edgeFinset m) o y) :
    connP (oddEdges G.edgeFinset m) o x :=
  Relation.ReflTransGen.trans hoy (connP_symm _ hxy)


theorem hnw_conn_trans_oy (m : Current V) {o x y : V}
    (hxy : connP (oddEdges G.edgeFinset m) x y) (hox : connP (oddEdges G.edgeFinset m) o x) :
    connP (oddEdges G.edgeFinset m) o y :=
  Relation.ReflTransGen.trans hox hxy









theorem hnw_gap_allConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_gap G β J m A o x y = -2 * hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hall
  unfold hnw_gap
  rw [hnw_switching G β J m hxy hxy' A, hnw_switching G β J m hoy hoy' A,
      hnw_switching G β J m hox hox' A]
  ring





theorem hnw_gap_noneConn (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnone : hnw_noneConn G m o x y) :
    hnw_gap G β J m A o x y = hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hnone
  unfold hnw_gap
  rw [hnw_mass_vanish G β J m hnd A hm hxy hxy',
      hnw_mass_vanish G β J m hnd A hm hoy hoy',
      hnw_mass_vanish G β J m hnd A hm hox hox']
  ring
















def hnw_coherent (m : Current V) (o x y : V) : Prop :=
  (connP (oddEdges G.edgeFinset m) x y ↔ connP (posEdges G.edgeFinset m) x y)
  ∧ (connP (oddEdges G.edgeFinset m) o y ↔ connP (posEdges G.edgeFinset m) o y)
  ∧ (connP (oddEdges G.edgeFinset m) o x ↔ connP (posEdges G.edgeFinset m) o x)







theorem hnw_gap_exactlyOne (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V) (hm : Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : hnw_coherent G m o x y)
    (hnotall : ¬ hnw_allConn G m o x y) (hnotnone : ¬ hnw_noneConn G m o x y) :
    hnw_gap G β J m A o x y = 0 := by
  obtain ⟨cxy, coy, cox⟩ := hcoh
  unfold hnw_allConn at hnotall
  unfold hnw_noneConn at hnotnone
  unfold hnw_gap
  by_cases oxy : connP (oddEdges G.edgeFinset m) x y <;>
    by_cases ooy : connP (oddEdges G.edgeFinset m) o y <;>
    by_cases oox : connP (oddEdges G.edgeFinset m) o x
  · exact absurd ⟨oxy, ooy, oox⟩ hnotall
  · exact absurd (hnw_conn_trans_ox G m oxy ooy) oox
  · exact absurd (hnw_conn_trans_oy G m oxy oox) ooy
  · rw [hnw_switching G β J m hxy oxy A,
        hnw_mass_vanish G β J m hnd A hm hoy (fun h => ooy (coy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hox (fun h => oox (cox.mpr h))]
    ring
  · exact absurd (hnw_conn_trans_xy G m ooy oox) oxy
  · rw [hnw_switching G β J m hoy ooy A,
        hnw_mass_vanish G β J m hnd A hm hxy (fun h => oxy (cxy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hox (fun h => oox (cox.mpr h))]
    ring
  · rw [hnw_switching G β J m hox oox A,
        hnw_mass_vanish G β J m hnd A hm hxy (fun h => oxy (cxy.mpr h)),
        hnw_mass_vanish G β J m hnd A hm hoy (fun h => ooy (coy.mpr h))]
    ring
  · exact absurd ⟨fun h => oxy (cxy.mpr h), fun h => ooy (coy.mpr h),
      fun h => oox (cox.mpr h)⟩ hnotnone















theorem hnw_inclusion_exclusion_decomp (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
    ∑ m ∈ M, hnw_gap G β J m A o x y
      = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A)
        - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) := by
  rw [← Finset.sum_filter_add_sum_filter_not M (fun m => hnw_allConn G m o x y)
    (fun m => hnw_gap G β J m A o x y)]
  have hall : ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_gap G β J m A o x y
      = -2 * ∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hmem => ?_)
    rw [Finset.mem_filter] at hmem
    exact hnw_gap_allConn G β J m A hox hoy hxy hmem.2
  have hrest : ∑ m ∈ M.filter (fun m => ¬ hnw_allConn G m o x y), hnw_gap G β J m A o x y
      = ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
    rw [← Finset.sum_filter_add_sum_filter_not (M.filter (fun m => ¬ hnw_allConn G m o x y))
      (fun m => hnw_noneConn G m o x y) (fun m => hnw_gap G β J m A o x y)]
    have hfilt : (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
        (fun m => hnw_noneConn G m o x y) = M.filter (fun m => hnw_noneConn G m o x y) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hm0, _⟩, hn⟩; exact ⟨hm0, hn⟩
      · rintro ⟨hm0, hn⟩
        exact ⟨⟨hm0, hnw_noneConn_not_allConn G m hn⟩, hn⟩
    have h1 : ∑ m ∈ (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
          (fun m => hnw_noneConn G m o x y), hnw_gap G β J m A o x y
        = ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
      rw [hfilt]
      refine Finset.sum_congr rfl (fun m hmem => ?_)
      rw [Finset.mem_filter] at hmem
      exact hnw_gap_noneConn G β J m (hnd m hmem.1) A (hm m hmem.1) hox hoy hxy hmem.2
    have h2 : ∑ m ∈ (M.filter (fun m => ¬ hnw_allConn G m o x y)).filter
          (fun m => ¬ hnw_noneConn G m o x y), hnw_gap G β J m A o x y = 0 := by
      refine Finset.sum_eq_zero (fun m hmem => ?_)
      simp only [Finset.mem_filter] at hmem
      exact hnw_gap_exactlyOne G β J m (hnd m hmem.1.1) A (hm m hmem.1.1) hox hoy hxy
        (hcoh m hmem.1.1) hmem.1.2 hmem.2
    rw [h1, h2, add_zero]
  rw [hall, hrest]; ring





















theorem hnw_closure_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y := by
  rw [hnw_inclusion_exclusion_decomp G β J M hnd A hm hox hoy hxy hcoh]
  linarith










theorem hnw_ghs_distinct_site_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}))
      ≤ ∑ m ∈ M, hnw_mass G β J m A := by
  have hge := hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom
  unfold hnw_gap at hge
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hge
  linarith

















theorem hnw_mass_eq_weight_mul_count (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V) :
    hnw_mass G β J m A
      = Sharpness.weight G β J m
        * ∑ K : {K : Current V // ∀ e, K e ≤ m e},
            (if Sharpness.sources G K.1 = A
              then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) := by
  unfold hnw_mass
  rw [ising_two_point_switching G β J m 1 A, one_mul]










theorem hnw_backbone_toggle_weight_preserving (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (P : Finset (Sym2 V)) {n : Current V} (hn : ∀ e, n e ≤ m e) :
    Sharpness.weight G β J (reflect m P n)
        * Sharpness.weight G β J (fun e => m e - reflect m P n e)
      = Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e) :=
  weight_reflect_split_eq G β J m P hn











theorem hnw_allMass_eq_paired (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hall : hnw_allConn G m o x y) :
    hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A
      ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A := by
  obtain ⟨hxy', hoy', hox'⟩ := hall
  exact ⟨hnw_switching G β J m hxy hxy' A, hnw_switching G β J m hoy hoy' A,
    hnw_switching G β J m hox hox' A⟩








theorem hnw_allConn_per_super_dom_iff (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (A : Finset V) :
    (2 * hnw_mass G β J m A ≤ 0) ↔ hnw_mass G β J m A = 0 := by
  have hnn := hnw_mass_nonneg G β J hβ hJ m A
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num











theorem hnw_sources_indicator (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) :
    Sharpness.sources G (fun e => if e ∈ P then 1 else 0) = srcP P := by
  ext z
  simp only [Sharpness.mem_sources, mem_srcP]
  have key : Sharpness.incidentFlux G (fun e => if e ∈ P then 1 else 0) z = degP P z := by
    unfold Sharpness.incidentFlux
    rw [degP_as_sum G.edgeFinset P hP z]
  rw [key]










theorem hnw_addBackbone_sources (m : Current V) (P : Finset (Sym2 V)) (hP : P ⊆ G.edgeFinset) :
    Sharpness.sources G (fun e => m e + (if e ∈ P then 1 else 0))
      = Sharpness.sources G m ∆ srcP P := by
  rw [show (fun e => m e + (if e ∈ P then 1 else 0))
      = fun e => m e + (fun e => if e ∈ P then 1 else 0) e from rfl,
      Sharpness.sources_add, hnw_sources_indicator G P hP]














theorem hnw_addBackbone_weight (β : ℝ) (J : Sym2 V → ℝ) (m : Current V)
    (P : Finset (Sym2 V)) :
    Sharpness.weight G β J (fun e => m e + (if e ∈ P then 1 else 0))
      = Sharpness.weight G β J m
        * ∏ e ∈ G.edgeFinset, (if e ∈ P then (β * J e) / (m e + 1) else 1) := by
  unfold Sharpness.weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : e ∈ P
  · simp only [if_pos h]
    rw [pow_succ]
    have hfac : (Nat.factorial (m e + 1) : ℝ) = (m e + 1) * Nat.factorial (m e) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    have hfacne : (Nat.factorial (m e) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  · simp only [if_neg h, add_zero, mul_one]

end Ising

end StatMech
