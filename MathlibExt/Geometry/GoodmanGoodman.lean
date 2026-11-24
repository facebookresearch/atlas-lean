/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/1121.lean` (the problem statement):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# The Goodman–Goodman circle covering theorem

`conjecture_holds` proves that a nonseparable finite family of Euclidean balls is covered
by a ball with radius the sum of its radii. For a nonempty family, the radius-weighted average
of the centers gives a covering center.
-/

@[expose] public section

namespace MathlibExt.Geometry.ErdosProblem1121Wanted

/-- **Erdős Problem 1121 (circle covering).** Write $B(c, r)$ for the closed ball with centre
$c$ and radius $r$ in Euclidean space $\mathbb{R}^d$. Call balls $B(c_1, r_1), \dots,
B(c_n, r_n)$ in $\mathbb{R}^d$ *nonseparable* if for every nonzero vector $v$ and every real
$t$ such that no point $p$ of any of the balls satisfies $\langle v, p \rangle = t$, either
$\langle v, c_i \rangle < t$ for all $i$ or $\langle v, c_i \rangle > t$ for all $i$. The
statement is the conjunction of two parts. First, for every natural number $n$, all points
$c_1, \dots, c_n \in \mathbb{R}^2$ and all reals $r_1, \dots, r_n > 0$ such that the discs
$B(c_i, r_i)$ are nonseparable, there is a point $z$ such that the closed disc
$B(z, r_1 + \dots + r_n)$ contains every $B(c_i, r_i)$. Second, the same holds in
$\mathbb{R}^d$ for every natural number $d$, with closed balls in place of discs. -/
def conjecture : Prop :=
  (∀ {n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin 2)) (r : Fin n → ℝ),
    (∀ i, 0 < r i) →
    (∀ (v : EuclideanSpace ℝ (Fin 2)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), @inner ℝ _ _ v p ≠ t) →
      (∀ i, @inner ℝ _ _ v (c i) < t) ∨ (∀ i, t < @inner ℝ _ _ v (c i))) →
    ∃ z : EuclideanSpace ℝ (Fin 2),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i)) ∧
  (∀ {d n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ),
    (∀ i, 0 < r i) →
    (∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), @inner ℝ _ _ v p ≠ t) →
      (∀ i, @inner ℝ _ _ v (c i) < t) ∨ (∀ i, t < @inner ℝ _ _ v (c i))) →
    ∃ z : EuclideanSpace ℝ (Fin d),
      (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i))

open Finset
open scoped RealInnerProductSpace

/-- If all the intervals indexed by a nonempty proper subset end at or before `b`, some
remaining interval must start at or before `b`, since a gap would separate the family. -/
private lemma exists_next_interval {ι : Type*} [Fintype ι] (a r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hgap : ∀ t, (∀ i, a i + r i < t ∨ t < a i - r i) →
      (∀ i, a i < t) ∨ (∀ i, t < a i))
    (s : Finset ι) (hs : s.Nonempty) (hs' : s ≠ univ) (b : ℝ)
    (hbound : ∀ i ∈ s, a i + r i ≤ b) : ∃ j ∉ s, a j - r j ≤ b := by
  classical
  have hc : sᶜ.Nonempty := nonempty_iff_ne_empty.mpr (mt (compl_eq_empty_iff s).mp hs')
  obtain ⟨j, hj, hmin⟩ := sᶜ.exists_min_image (fun i ↦ a i - r i) hc
  refine ⟨j, mem_compl.mp hj, ?_⟩
  by_contra! h
  obtain ⟨t, hbt, htj⟩ := exists_between h
  have hside := hgap t fun i ↦ by
    by_cases hi : i ∈ s
    · exact Or.inl ((hbound i hi).trans_lt hbt)
    · exact Or.inr (htj.trans_le (hmin i (mem_compl.mpr hi)))
  obtain hleft | hright := hside
  · linarith [hleft j, hr j]
  · obtain ⟨i, hi⟩ := hs
    linarith [hright i, hbound i hi, hr i]

/-- For intervals with no separating gap, if one interval starts at or before zero,
the first moment of their centers with weights `r` is at most the square of the total weight. -/
private lemma interval_moment_le {ι : Type*} [Fintype ι] (a r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hgap : ∀ t, (∀ i, a i + r i < t ∨ t < a i - r i) →
      (∀ i, a i < t) ∨ (∀ i, t < a i))
    (hstart : ∃ i, a i ≤ r i) : ∑ i, r i * a i ≤ (∑ i, r i) ^ 2 := by
  classical
  -- For a partial family of total weight R, keep all its right endpoints at most 2R
  -- and its first moment at most R². The next center is at most 2R + r.
  have grow (s : Finset ι) (hs : s.Nonempty)
      (he : ∀ i ∈ s, a i + r i ≤ 2 * ∑ k ∈ s, r k)
      (hm : ∑ i ∈ s, r i * a i ≤ (∑ i ∈ s, r i) ^ 2) :
      ∑ i, r i * a i ≤ (∑ i, r i) ^ 2 := by
    induction s using Finset.strongDownwardInductionOn (n := Fintype.card ι) with
    | H s ih _ =>
      by_cases hall : s = univ
      · simpa only [hall] using hm
      obtain ⟨j, hj, htouch⟩ := exists_next_interval a r hr hgap s hs hall _ he
      refine ih (card_le_univ _) (ssubset_insert hj) (insert_nonempty ..) ?_ ?_
      · rw [sum_insert hj]
        intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · linarith
        · linarith [he i hi, hr j]
      · rw [sum_insert hj, sum_insert hj]
        nlinarith [mul_le_mul_of_nonneg_left htouch (hr j)]
    | _ => exact card_le_univ _
  obtain ⟨i, hi⟩ := hstart
  refine grow {i} (singleton_nonempty i) ?_ ?_
  · simpa using (show a i + r i ≤ 2 * r i by linarith)
  · simpa [sq] using mul_le_mul_of_nonneg_left hi (hr i)

/-- Project from a covered point toward the radius-weighted center and apply the interval bound. -/
private lemma cover {d n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 →
      (∀ i, ∀ p ∈ Metric.closedBall (c i) (r i), ⟪v, p⟫ ≠ t) →
      (∀ i, ⟪v, c i⟫ < t) ∨ (∀ i, t < ⟪v, c i⟫)) :
    ∃ z, (⋃ i, Metric.closedBall (c i) (r i)) ⊆ Metric.closedBall z (∑ i, r i) := by
  let R := ∑ i, r i
  let z := R⁻¹ • ∑ i, r i • c i
  refine ⟨z, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  have hR : 0 < R := sum_pos' (fun j _ ↦ (hr j).le) ⟨i, mem_univ i, hr i⟩
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  by_cases hz : z - p = 0
  · simpa [hz] using hR.le
  let v := ‖z - p‖⁻¹ • (z - p)
  have hv : ‖v‖ = 1 := norm_smul_inv_norm hz
  have hv₀ : v ≠ 0 := by
    rintro h
    simp [h] at hv
  let a := fun j ↦ ⟪v, c j⟫ - ⟪v, p⟫
  have hproj (j) (q) (hq : q ∈ Metric.closedBall (c j) (r j)) :
      |⟪v, q⟫ - ⟪v, c j⟫| ≤ r j := by
    rw [← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simpa only [hv, one_mul, ← dist_eq_norm] using Metric.mem_closedBall.mp hq
  have hgap (t : ℝ) (ht : ∀ j, a j + r j < t ∨ t < a j - r j) :
      (∀ j, a j < t) ∨ (∀ j, t < a j) := by
    obtain h | h := hns v (t + ⟪v, p⟫) hv₀ fun j q hq heq ↦ by
      have hb := abs_le.mp (hproj j q hq)
      rcases ht j with hj | hj <;> dsimp [a] at hj <;> linarith
    · exact Or.inl fun j ↦ sub_lt_iff_lt_add.mpr (h j)
    · exact Or.inr fun j ↦ lt_sub_iff_add_lt.mpr (h j)
  have hstart : a i ≤ r i := by
    dsimp [a]
    linarith [(abs_le.mp (hproj i p hi)).1]
  have hm := interval_moment_le a r (fun j ↦ (hr j).le) hgap ⟨i, hstart⟩
  have hmoment : ∑ j, r j * a j = R * ⟪v, z - p⟫ := by
    simp only [a, z, inner_sub_right, inner_smul_right, inner_sum, mul_sub, sum_sub_distrib,
      ← sum_mul, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, R]
  have hdir : ⟪v, z - p⟫ = ‖z - p‖ := by
    rw [show v = _ from rfl, real_inner_smul_left, real_inner_self_eq_norm_sq, sq,
      inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hz)]
  rw [hmoment, hdir] at hm
  exact le_of_mul_le_mul_left (by simpa only [sq] using hm : R * ‖z - p‖ ≤ R * R) hR

/--
**Circle covering theorem (Erdős Problem 1121).** Both parts of Erdős Problem 1121 hold. For
every natural number $d$, and in particular in the plane ($d = 2$): if $B(c_1, r_1), \dots,
B(c_n, r_n)$ are closed balls in Euclidean space $\mathbb{R}^d$ with centres $c_i$ and radii
$r_i > 0$ such that every hyperplane meeting none of the balls has all the centres $c_i$
strictly on the same side, then some closed ball of radius $r_1 + \dots + r_n$ contains all of
the balls.

Goodman and Goodman [GoGo45] proved this in the plane and in higher dimensions; Hadwiger [Ha47]
extended it to convex bodies.

Source: Goodman and Goodman [GoGo45] (planar
case and higher dimensions), per erdosproblems.com/1121, https://www.erdosproblems.com/1121.
Moved from `OpenConjectures/Geometry/ErdosProblem1121`.
-/
theorem conjecture_holds : conjecture := ⟨cover, cover⟩

end MathlibExt.Geometry.ErdosProblem1121Wanted
