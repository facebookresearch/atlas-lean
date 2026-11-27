/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Edge functions for a triangle

The edge-function test used in Pineda's *A parallel algorithm for polygon rasterization*
(SIGGRAPH 1988) uses the signed area along each directed edge. We use the convention that
`cross (v - u) (x - u)` is positive on the left of the directed edge from `u` to `v`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Set

private theorem cross_cyclic (a b c : ℝ × ℝ) :
    cross (c - b) (a - b) = cross (b - a) (c - a) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  ring

private theorem triangle_subset_edge_halfSpace {a b c : ℝ × ℝ}
    (hc : 0 ≤ cross (b - a) (c - a)) :
    _root_.convexHull ℝ {a, b, c} ⊆ {x | 0 ≤ cross (b - a) (x - a)} := by
  apply convexHull_min
  · intro x hx
    rcases (show x = a ∨ x = b ∨ x = c by simpa only [mem_insert_iff, mem_singleton_iff] using hx)
      with rfl | rfl | rfl
    · simp [cross]
    · simp [cross]
    · exact hc
  · rw [convex_iff_add_mem]
    intro x hx y hy r s hr hs hrs
    have h_affine : cross (b - a) (r • x + s • y - a) =
        r * cross (b - a) (x - a) + s * cross (b - a) (y - a) := by
      have hs' : s = 1 - r := by linarith
      simp only [hs', cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [mem_ofPred_eq, h_affine]
    exact add_nonneg (mul_nonneg hr hx) (mul_nonneg hs hy)

private theorem mem_triangle_of_edge_nonneg {a b c x : ℝ × ℝ}
    (h : 0 < cross (b - a) (c - a)) (hab : 0 ≤ cross (b - a) (x - a))
    (hbc : 0 ≤ cross (c - b) (x - b)) (hca : 0 ≤ cross (a - c) (x - c)) :
    x ∈ _root_.convexHull ℝ {a, b, c} := by
  -- The edge opposite each vertex gives its barycentric weight after normalization.
  let d := cross (b - a) (c - a)
  let α := cross (c - b) (x - b) / d
  let β := cross (a - c) (x - c) / d
  let γ := cross (b - a) (x - a) / d
  have hd : d ≠ 0 := h.ne'
  have hsum : α + β + γ = 1 := by
    dsimp only [α, β, γ]
    rw [← add_div, ← add_div, (div_eq_iff hd), one_mul]
    simp only [d, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hx : α • a + β • b + γ • c = x := by
    apply Prod.ext <;>
      simp only [α, β, γ, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
      field_simp [hd] <;>
      simp only [d, cross, Prod.fst_sub, Prod.snd_sub] <;> ring
  refine mem_convexHull_of_exists_fintype ![α, β, γ] ![a, b, c] ?_ ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact div_nonneg hbc h.le
    · exact div_nonneg hca h.le
    · exact div_nonneg hab h.le
  · simpa [Fin.sum_univ_three] using hsum
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_three] using hx

private theorem continuous_edge (a b : ℝ × ℝ) :
    Continuous (fun x : ℝ × ℝ => cross (b - a) (x - a)) := by
  simp only [cross, Prod.fst_sub, Prod.snd_sub]
  fun_prop

private theorem edge_pos_of_mem_interior {s : Set (ℝ × ℝ)} {a b c x : ℝ × ℝ}
    (hs : s ⊆ {y | 0 ≤ cross (b - a) (y - a)}) (hc : 0 < cross (b - a) (c - a))
    (hx : x ∈ interior s) : 0 < cross (b - a) (x - a) := by
  by_contra! h
  have he : cross (b - a) (x - a) = 0 := le_antisymm h (hs (interior_subset hx))
  -- On an open neighborhood of `0`, the line through `x` in direction `c - a`
  -- must stay in the interior. But every negative parameter leaves the half-space.
  let line (t : ℝ) := x + t • (c - a)
  have hline : Continuous line := by
    dsimp only [line]
    fun_prop
  have hsubset : line ⁻¹' interior s ⊆ Ici (0 : ℝ) := by
    intro t ht
    have ht' : 0 ≤ cross (b - a) (line t - a) := hs (interior_subset ht)
    have heq : cross (b - a) (line t - a) =
        cross (b - a) (x - a) + t * cross (b - a) (c - a) := by
      simp only [line, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [heq, he, zero_add] at ht'
    exact (mul_nonneg_iff_of_pos_right hc).mp ht'
  have hzero : (0 : ℝ) ∈ line ⁻¹' interior s := by simpa [line] using hx
  have hmem := interior_maximal hsubset (isOpen_interior.preimage hline) hzero
  rw [interior_Ici] at hmem
  exact (lt_irrefl (0 : ℝ)) hmem

/-- **Edge-function test for a triangle.** If `a`, `b`, and `c` are counterclockwise and
noncollinear, a point `x` belongs to their closed triangle (the convex hull of the vertices)
exactly when all three directed edge values are nonnegative. It belongs to the topological
interior of that hull exactly when all three are positive. The edge value for `u` to `v` is
`cross (v - u) (x - u)`, twice the signed area of the triangle with vertices `u`, `v`, `x`. -/
theorem triangle_mem_iff_edge_signs (a b c x : ℝ × ℝ) (h : 0 < cross (b - a) (c - a)) :
    (x ∈ _root_.convexHull ℝ {a, b, c} ↔
      0 ≤ cross (b - a) (x - a) ∧ 0 ≤ cross (c - b) (x - b) ∧ 0 ≤ cross (a - c) (x - c)) ∧
    (x ∈ interior (_root_.convexHull ℝ {a, b, c}) ↔
      0 < cross (b - a) (x - a) ∧ 0 < cross (c - b) (x - b) ∧ 0 < cross (a - c) (x - c)) := by
  have hbc : 0 < cross (c - b) (a - b) := cross_cyclic a b c ▸ h
  have hca : 0 < cross (a - c) (b - c) := cross_cyclic b c a ▸ hbc
  have rotate₁ : ({b, c, a} : Set (ℝ × ℝ)) = {a, b, c} := by
    rw [pair_comm c a, insert_comm b a]
  have rotate₂ : ({c, a, b} : Set (ℝ × ℝ)) = {a, b, c} := by
    rw [insert_comm c a, pair_comm c b]
  have habHull := triangle_subset_edge_halfSpace h.le
  have hbcHull := rotate₁ ▸ triangle_subset_edge_halfSpace hbc.le
  have hcaHull := rotate₂ ▸ triangle_subset_edge_halfSpace hca.le
  have closed_iff (y : ℝ × ℝ) : y ∈ _root_.convexHull ℝ {a, b, c} ↔
      0 ≤ cross (b - a) (y - a) ∧ 0 ≤ cross (c - b) (y - b) ∧ 0 ≤ cross (a - c) (y - c) :=
    ⟨fun hy => ⟨habHull hy, hbcHull hy, hcaHull hy⟩,
      fun ⟨hy₁, hy₂, hy₃⟩ => mem_triangle_of_edge_nonneg h hy₁ hy₂ hy₃⟩
  refine ⟨closed_iff x, ?_, ?_⟩
  · intro hx
    exact ⟨edge_pos_of_mem_interior habHull h hx, edge_pos_of_mem_interior hbcHull hbc hx,
      edge_pos_of_mem_interior hcaHull hca hx⟩
  · intro hx
    have hopen : IsOpen {y : ℝ × ℝ |
        0 < cross (b - a) (y - a) ∧ 0 < cross (c - b) (y - b) ∧ 0 < cross (a - c) (y - c)} :=
      (isOpen_lt continuous_const (continuous_edge a b)).inter
        ((isOpen_lt continuous_const (continuous_edge b c)).inter
          (isOpen_lt continuous_const (continuous_edge c a)))
    refine interior_maximal ?_ hopen hx
    intro y hy
    obtain ⟨hy₁, hy₂, hy₃⟩ := hy
    exact (closed_iff y).2 ⟨hy₁.le, hy₂.le, hy₃.le⟩

end Cslib.Algorithms.Lean.Geometry
