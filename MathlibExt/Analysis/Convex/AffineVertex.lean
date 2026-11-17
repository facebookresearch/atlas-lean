/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine vertex certificates for fixed schedules

## i. Overview

An affine inequality holds on the convex hull of a finite vertex set
exactly when it holds at every vertex. In schedule form: with fixed
starts and affine durations, every precedence inequality over a
scenario hull is certified by its vertex values, and duration
nonnegativity is checked the same way, separately.

## ii. Key results

- `AffineVertex.affineFun_nonneg_hull_iff`: the vertex certificate.
- `AffineVertex.schedule_precedence_hull_iff`: all precedence
  inequalities over the hull.
- `AffineVertex.durations_nonneg_hull_iff`: duration nonnegativity.

## iii. Table of contents

- A. Affine vertex certificates

## iv. References

- Standard finite convex-hull arguments; schedule form as in
  robust project scheduling with affine duration uncertainty.

## A. Affine vertex certificates
-/

@[expose] public section

namespace AffineVertex

open Finset

/-- An affine function on `ι → ℝ` in coefficient form. -/
noncomputable def affineFun {ι : Type*} [Fintype ι] (c : ℝ) (p : ι → ℝ) (x : ι → ℝ) : ℝ :=
  c + ∑ i, p i * x i

theorem affineFun_convex_comb {ι : Type*} [Fintype ι]
    (c : ℝ) (p : ι → ℝ) (x y : ι → ℝ) (a b : ℝ) (h : a + b = 1) :
    affineFun c p (a • x + b • y) = a * affineFun c p x + b * affineFun c p y := by
  have hterm : ∀ i, p i * (a * x i + b * y i)
      = a * (p i * x i) + b * (p i * y i) := fun i => by ring
  simp only [affineFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  linear_combination -c * h

/-- An affine inequality holds on the whole convex hull of a finite
nonempty vertex set exactly when it holds at every vertex. This is
the fixed-schedule vertex certificate: precedence inequalities with
affine durations need only be checked at hull vertices. -/
theorem affineFun_nonneg_hull_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ)) (hs : s.Nonempty)
    (c : ℝ) (p : ι → ℝ) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), 0 ≤ affineFun c p x)
      ↔ ∀ v ∈ s, 0 ≤ affineFun c p v := by
  have _ := hs
  constructor
  · intro h v hv
    exact h v (subset_convexHull ℝ (s : Set (ι → ℝ)) (Finset.mem_coe.mpr hv))
  · intro hv x hx
    have hconv : Convex ℝ {x : ι → ℝ | 0 ≤ affineFun c p x} := by
      intro x hx y hy a b ha hb hab
      show 0 ≤ affineFun c p (a • x + b • y)
      rw [affineFun_convex_comb c p x y a b hab]
      exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    have hsub : (s : Set (ι → ℝ)) ⊆ {x : ι → ℝ | 0 ≤ affineFun c p x} :=
      fun v hvm => hv v (Finset.mem_coe.mp hvm)
    exact convexHull_min hsub hconv hx

/-- Forward form used by consumers: vertex checks certify the hull. -/
theorem affineFun_nonneg_of_vertices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ)) (hs : s.Nonempty)
    (c : ℝ) (p : ι → ℝ)
    (hv : ∀ v ∈ s, 0 ≤ affineFun c p v)
    {x : ι → ℝ} (hx : x ∈ convexHull ℝ (s : Set (ι → ℝ))) :
    0 ≤ affineFun c p x := by
  exact (affineFun_nonneg_hull_iff s hs c p).mpr hv x hx

theorem schedule_edge_rewrite {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (S a : J → ℝ) (b : J → ι → ℝ) (e : J × J) (x : ι → ℝ) :
    (S e.1 + affineFun (a e.1) (b e.1) x ≤ S e.2)
      ↔ 0 ≤ affineFun (S e.2 - S e.1 - a e.1) (-b e.1) x := by
  have hsum : (∑ i, (-b e.1) i * x i) = -(∑ i, (b e.1) i * x i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.neg_apply]
    ring
  simp only [affineFun, hsum]
  constructor <;> intro h <;> linarith

/-- Schedule bridge: with start-time map `S`, per-activity affine
durations `affineFun (a j) (b j)`, and precedence table `E` (edge
`(i, j)`: `S i + d_i(x) ≤ S j`), every precedence inequality holds
over the whole scenario hull exactly when it holds at every vertex. -/
theorem schedule_precedence_hull_iff {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ)) (hs : s.Nonempty)
    (S a : J → ℝ) (b : J → ι → ℝ) (E : Finset (J × J)) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), ∀ e ∈ E,
        S e.1 + affineFun (a e.1) (b e.1) x ≤ S e.2)
      ↔ ∀ v ∈ s, ∀ e ∈ E, S e.1 + affineFun (a e.1) (b e.1) v ≤ S e.2 := by
  constructor
  · intro h v hv e he
    exact (schedule_edge_rewrite S a b e v).mpr
      ((affineFun_nonneg_hull_iff s hs (S e.2 - S e.1 - a e.1) (-b e.1)).mp
        (fun x hx => (schedule_edge_rewrite S a b e x).mp (h x hx e he)) v hv)
  · intro h x hx e he
    exact (schedule_edge_rewrite S a b e x).mpr
      ((affineFun_nonneg_hull_iff s hs (S e.2 - S e.1 - a e.1) (-b e.1)).mpr
        (fun v hv => (schedule_edge_rewrite S a b e v).mp (h v hv e he)) x hx)

/-- Duration nonnegativity over the hull, checked separately at the
vertices, for every activity in `A`. -/
theorem durations_nonneg_hull_iff {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ)) (hs : s.Nonempty) (A : Finset J)
    (a : J → ℝ) (b : J → ι → ℝ) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), ∀ j ∈ A, 0 ≤ affineFun (a j) (b j) x)
      ↔ ∀ v ∈ s, ∀ j ∈ A, 0 ≤ affineFun (a j) (b j) v := by
  constructor
  · intro h v hv j hj
    exact (affineFun_nonneg_hull_iff s hs (a j) (b j)).mp
      (fun x hx => h x hx j hj) v hv
  · intro h x hx j hj
    exact (affineFun_nonneg_hull_iff s hs (a j) (b j)).mpr
      (fun v hv => h v hv j hj) x hx

end AffineVertex
