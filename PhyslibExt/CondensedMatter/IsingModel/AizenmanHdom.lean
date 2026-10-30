/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.AizenmanInclusionExclusion

/-!
# The domination condition of the random-current GHS argument

Rerouting along backbones, the domination condition, and a triangle counterexample to it.

## i. Overview

When a current connects all three pairs among `o, x, y`, there are sub-currents with sources `{o,
x}` and `{x, y}`, and symmetric difference with them permutes the source classes; this computes the
gap on such currents. The nonnegativity of the total gap is equivalent to the domination condition
`2 · mass(all connected) ≤ mass(none connected)`. On the triangle with one current through all three
edges the condition fails (`ahd_hdom_refutable`).

## ii. Key results

- `StatMech.Ising.ahd_backbone_exists` : backbones between connected sites
- `StatMech.Ising.ahd_closure_iff_hdom` : nonnegative total gap iff domination
- `StatMech.Ising.ahd_triEnds` : the triangle
- `StatMech.Ising.ahd_hdom_refutable` : the domination condition fails on the triangle

## iii. Table of contents

- A. Backbones and rerouting
- B. The domination condition
- C. A counterexample on the triangle

## iv. References

- M. Aizenman, *Geometric analysis of φ⁴ fields and Ising models. Parts I and II*, Comm. Math. Phys.
  86 (1982) 1–48
-/

@[expose] public section

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]

/-! ## A. Backbones and rerouting -/

lemma ahd_backbone_exists (ends : ι → Sym2 V) (m : Finset ι) {o x y : V}
    (hall : aie_allConn ends m o x y) (hox : o ≠ x) (hxy : x ≠ y) :
    (∃ P ⊆ m, sources ends P = {o, x}) ∧ (∃ Q ⊆ m, sources ends Q = {x, y}) := by
  obtain ⟨hxy', _hoy', hox'⟩ := hall
  exact ⟨exists_conn_set ends m hox' hox, exists_conn_set ends m hxy' hxy⟩

lemma ahd_mass_reroute_xy_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {x, y}) = aie_mass ends m φ A := by
  obtain ⟨hxy', _, _⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hxy φ hφ, ite_eq_left hxy', one_mul]

lemma ahd_mass_reroute_oy_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hoy : o ≠ y) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, y}) = aie_mass ends m φ A := by
  obtain ⟨_, hoy', _⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hoy φ hφ, ite_eq_left hoy', one_mul]

lemma ahd_mass_reroute_ox_eq (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (φ : Finset ι → ℝ)
    (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, x}) = aie_mass ends m φ A := by
  obtain ⟨_, _, hox'⟩ := hall
  unfold aie_mass
  rw [asd_switching_weighted_indicator ends m hnd A hm hox φ hφ, ite_eq_left hox', one_mul]

lemma ahd_mass_reroute₂_eq (ends : ι → Sym2 V) (m : Finset ι) (A : Finset V)
    {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφ2 : ∀ K P Q, P ⊆ m → Q ⊆ m → K ⊆ m → φ ((K ∆ P) ∆ Q) = φ K)
    (hall : aie_allConn ends m o x y) :
    aie_mass ends m φ (A ∆ {o, x} ∆ {x, y}) = aie_mass ends m φ A := by
  obtain ⟨hxy', _, hox'⟩ := hall
  unfold aie_mass
  exact asd_signDominance₂_edgecopy ends m A hox hxy hox' hxy' φ hφ2

/-! ## B. The domination condition -/

lemma ahd_per_super_allConn_gap_nonneg_iff (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (φ : Finset ι → ℝ)
    (hφnn : ∀ K, 0 ≤ φ K) (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
    (hall : aie_allConn ends m o x y) :
    0 ≤ aie_gap ends m φ A o x y ↔ aie_mass ends m φ A = 0 := by
  rw [aie_gap_allConn ends m hnd A hm hox hoy hxy φ hφ hall]
  have hnn := aie_mass_nonneg ends m φ hφnn A
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

lemma ahd_closure_iff_hdom (ends : ι → Sym2 V) (M : Finset (Finset ι))
    (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, sources ends m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (Φ : Finset ι → Finset ι → ℝ)
    (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
    (0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y)
      ↔ (2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A)
          ≤ ∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) := by
  rw [aie_inclusion_exclusion_decomp ends M hnd A hm hox hoy hxy Φ hΦ]
  constructor <;> intro h <;> linarith

/-! ## C. A counterexample on the triangle -/

/-- The three edges `{0, 1}`, `{1, 2}`, `{0, 2}` of the triangle on `Fin 3`. -/
def ahd_triEnds : Fin 3 → Sym2 (Fin 3)
  | 0 => s(0, 1)
  | 1 => s(1, 2)
  | 2 => s(0, 2)

lemma ahd_triEnds_nd : ∀ i ∈ ({0, 1, 2} : Finset (Fin 3)), ¬ (ahd_triEnds i).IsDiag := by
  decide

lemma ahd_tri_conn_ox : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩

lemma ahd_tri_conn_xy : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩

lemma ahd_tri_conn_oy : connK ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 2 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩

lemma ahd_tri_allConn :
    aie_allConn ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 1 2 :=
  ⟨ahd_tri_conn_xy, ahd_tri_conn_oy, ahd_tri_conn_ox⟩

lemma ahd_tri_mass_pos :
    (0 : ℝ) < aie_mass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1)
      (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) := by
  unfold aie_mass
  apply Finset.sum_pos (fun K _ => by norm_num)
  exact ⟨({0, 1, 2} : Finset (Fin 3)), by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, rfl⟩⟩

/-- The domination condition fails for the single current through all edges of the triangle. -/
lemma ahd_hdom_refutable :
    ¬ (2 * (∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_allConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3))))
        ≤ ∑ m ∈ ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))).filter
              (fun m => aie_noneConn ahd_triEnds m 0 1 2),
            aie_mass ahd_triEnds m (fun _ => 1)
              (sources ahd_triEnds ({0, 1, 2} : Finset (Fin 3)))) := by
  intro hdom
  set m₀ : Finset (Fin 3) := {0, 1, 2} with hm₀
  set A₀ : Finset (Fin 3) := sources ahd_triEnds m₀ with hA₀
  have hall : aie_allConn ahd_triEnds m₀ 0 1 2 := ahd_tri_allConn
  have hnotnone : ¬ aie_noneConn ahd_triEnds m₀ 0 1 2 := by
    rintro ⟨h1, _, _⟩; exact h1 hall.1
  rw [Finset.filter_singleton, ite_eq_left hall, Finset.sum_singleton,
      Finset.filter_singleton, ite_eq_right hnotnone, Finset.sum_empty] at hdom
  have hpos : (0 : ℝ) < aie_mass ahd_triEnds m₀ (fun _ => 1) A₀ := ahd_tri_mass_pos
  linarith

end RandomCurrent

end Sharpness

end StatMech
