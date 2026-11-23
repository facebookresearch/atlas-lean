/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.AizenmanHdom

/-!
# Backbone-conditioned decomposition of the random-current GHS gap

The GHS gap conditioned on the cluster of `o`, and the failure of the conditioned domination
condition.

## i. Overview

Grouping sub-currents by the cluster (backbone) of `o`, all three pairs among `o, x, y` are
connected exactly when `x` and `y` lie in the cluster of `o`. The GHS gap then decomposes into
per-backbone terms, each controlled by sign dominance, and the total gap is nonnegative under a
conditioned domination condition. That condition also fails on the triangle
(`atb_conditionedDom_refutable`).

## ii. Key results

- `StatMech.Ising.atb_backbone` : the cluster of `o` in a current
- `StatMech.Ising.atb_conditioned_decomp` : the backbone-conditioned decomposition
- `StatMech.Ising.atb_conditionedDom` : the conditioned domination condition
- `StatMech.Ising.atb_conditioned_closure` : nonnegative total gap under conditioned domination
- `StatMech.Ising.atb_conditionedDom_refutable` : the condition fails on the triangle

## iii. Table of contents

- A. The backbone of a current
- B. Conditioned gaps
- C. The conditioned domination condition

## iv. References

- M. Aizenman, *Geometric analysis of φ⁴ fields and Ising models. Parts I and II*, Comm. Math. Phys.
  86 (1982) 1–48
-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech

namespace Ising

open StatMech.Sharpness.RandomCurrent

local notation "srcK" => StatMech.Sharpness.RandomCurrent.sources
local notation "compK" => StatMech.Sharpness.RandomCurrent.compOf

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]

/-! ## A. The backbone of a current -/

/-- The cluster of `o` in the current `m`: the sites connected to `o` by edges of `m`. -/
noncomputable def atb_backbone (ends : ι → Sym2 V) (m : Finset ι) (o : V) : Finset V :=
  compK ends m o

omit [DecidableEq ι] [DecidableEq V] [Fintype ι] in
lemma atb_conn_iff_mem_backbone (ends : ι → Sym2 V) (m : Finset ι) (o z : V) :
    connK ends m o z ↔ z ∈ atb_backbone ends m o := by
  unfold atb_backbone StatMech.Sharpness.RandomCurrent.compOf
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma atb_conn_xy_of_mem_backbone (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    connK ends m x y := by
  rw [← atb_conn_iff_mem_backbone] at hx hy
  exact Relation.ReflTransGen.trans (connK_symm ends m hx) hy

lemma atb_allConn_of_xy_in_backbone (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    aie_allConn ends m o x y := by
  have hox : connK ends m o x := (atb_conn_iff_mem_backbone ends m o x).2 hx
  have hoy : connK ends m o y := (atb_conn_iff_mem_backbone ends m o y).2 hy
  exact ⟨atb_conn_xy_of_mem_backbone ends m hx hy, hoy, hox⟩

lemma atb_allConn_iff_xy_in_backbone (ends : ι → Sym2 V) (m : Finset ι) (o x y : V) :
    aie_allConn ends m o x y
      ↔ (x ∈ atb_backbone ends m o ∧ y ∈ atb_backbone ends m o) := by
  constructor
  · rintro ⟨_, hoy, hox⟩
    exact ⟨(atb_conn_iff_mem_backbone ends m o x).1 hox,
           (atb_conn_iff_mem_backbone ends m o y).1 hoy⟩
  · rintro ⟨hx, hy⟩
    exact atb_allConn_of_xy_in_backbone ends m hx hy

lemma atb_signDominance_per_backbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {u v : V} (huv : u ≠ v) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_mass ends m φ (A ∆ {u, v}) ≤ aie_mass ends m φ A := by
  unfold aie_mass
  exact asd_signDominance ends m hnd A hm huv φ hφnn (fun K P hP hK => hφ K P hP hK)

/-! ## B. Conditioned gaps -/

lemma atb_conditioned_gap_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
    aie_gap ends m φ A o x y = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y :=
  aie_gap_eq ends m hnd A hm hox hoy hxy φ hφ

lemma atb_conditioned_gap_allBackbone (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hx : x ∈ atb_backbone ends m o) (hy : y ∈ atb_backbone ends m o) :
    aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A :=
  aie_gap_allConn ends m hnd A hm hox hoy hxy φ hφ
    (atb_allConn_of_xy_in_backbone ends m hx hy)

lemma atb_conditioned_decomp (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    ∑ m ∈ M, aie_gap ends m (Φ m) A o x y
      = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A)
        - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) :=
  aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ

/-! ## C. The conditioned domination condition -/

/-- The domination condition `2 · mass(all connected) ≤ mass(none connected)`, summed over
currents in `M`. -/
def atb_conditionedDom (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (o x y : V) (Φ : Finset ι → Finset ι → ℝ) : Prop :=
  2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
    ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A

omit [DecidableEq ι] [Fintype ι] in
lemma atb_conditionedDom_holds_of_no_allConn (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (A : Finset V) {o x y : V} (Φ : Finset ι → Finset ι → ℝ)
    (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
    (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
    atb_conditionedDom ends M A o x y Φ := by
  unfold atb_conditionedDom
  rw [hno, Finset.sum_empty, mul_zero]
  exact Finset.sum_nonneg (fun m _ => aie_mass_nonneg ends m (Φ m) (hΦnn m) A)

lemma atb_conditioned_closure (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, srcK ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
    (hdom : atb_conditionedDom ends M A o x y Φ) :
    0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y :=
  aie_inclusion_exclusion ends M hnd A hm hox hoy hxy Φ hΦ hdom

lemma atb_tri_x_in_backbone :
    (1 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 :=
  (atb_conn_iff_mem_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1).1 ahd_tri_conn_ox

lemma atb_tri_y_in_backbone :
    (2 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 :=
  (atb_conn_iff_mem_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 2).1 ahd_tri_conn_oy

lemma atb_conditionedDom_refutable :
    ¬ atb_conditionedDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3)))
        (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
  unfold atb_conditionedDom
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := srcK ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 :=
    (atb_allConn_iff_xy_in_backbone ahd_triEnds m₀ 0 1 2).2
      ⟨atb_tri_x_in_backbone, atb_tri_y_in_backbone⟩
  have hnotnone : ¬ aie_noneConn ahd_triEnds m₀ 0 1 2 := by
    rintro ⟨h1, _, _⟩; exact h1 hall.1
  rw [Finset.filter_singleton, ite_eq_left hall, Finset.sum_singleton,
      Finset.filter_singleton, ite_eq_right hnotnone, Finset.sum_empty] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end Ising

end StatMech
