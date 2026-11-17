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
    (c : ℝ) (p : ι → ℝ) (x y : ι → ℝ) (a b : ℝ) (hab : a + b = 1) :
    affineFun c p (a • x + b • y) = a * affineFun c p x + b * affineFun c p y := by
  have hterm : ∀ i, p i * (a * x i + b * y i) = a * (p i * x i) + b * (p i * y i) :=
    fun i => by ring
  simp only [affineFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hterm,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  linarith

theorem precedence_le_iff {ι : Type*} [Fintype ι]
    (S1 S2 a : ℝ) (b : ι → ℝ) (x : ι → ℝ) :
    (S1 + affineFun a b x ≤ S2)
      ↔ 0 ≤ affineFun (S2 - S1 - a) (fun i => -(b i)) x := by
  simp only [affineFun, neg_mul, Finset.sum_neg_distrib]
  constructor <;> intro h <;> linarith

/-- An affine inequality holds on the whole convex hull of a finite
possibly empty finite vertex set exactly when it holds at every vertex. This is
the fixed-schedule vertex certificate: precedence inequalities with
affine durations need only be checked at hull vertices. -/
theorem affineFun_nonneg_hull_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ))
    (c : ℝ) (p : ι → ℝ) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), 0 ≤ affineFun c p x)
      ↔ ∀ v ∈ s, 0 ≤ affineFun c p v := by
  constructor
  · intro h v hv
    exact h v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
  · intro hv x hx
    have hconv : Convex ℝ {x | 0 ≤ affineFun c p x} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [affineFun_convex_comb c p x y a b hab]
      exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    have hsub : (s : Set (ι → ℝ)) ⊆ {x | 0 ≤ affineFun c p x} := by
      intro v hvmem
      exact hv v (Finset.mem_coe.mp hvmem)
    exact convexHull_min hsub hconv hx

/-- Forward form used by consumers: vertex checks certify the hull. -/
theorem affineFun_nonneg_of_vertices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ))
    (c : ℝ) (p : ι → ℝ)
    (hv : ∀ v ∈ s, 0 ≤ affineFun c p v)
    {x : ι → ℝ} (hx : x ∈ convexHull ℝ (s : Set (ι → ℝ))) :
    0 ≤ affineFun c p x := by
  exact (affineFun_nonneg_hull_iff s c p).mpr hv x hx

/-- Schedule bridge: with start-time map `S`, per-activity affine
durations `affineFun (a j) (b j)`, and precedence table `E` (edge
`(i, j)`: `S i + d_i(x) ≤ S j`), every precedence inequality holds
over the whole scenario hull exactly when it holds at every vertex. -/
theorem schedule_precedence_hull_iff {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ))
    (S a : J → ℝ) (b : J → ι → ℝ) (E : Finset (J × J)) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), ∀ e ∈ E,
        S e.1 + affineFun (a e.1) (b e.1) x ≤ S e.2)
      ↔ ∀ v ∈ s, ∀ e ∈ E, S e.1 + affineFun (a e.1) (b e.1) v ≤ S e.2 := by
  constructor
  · intro h v hv e he
    exact h v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)) e he
  · intro h x hx e he
    have hper : ∀ v ∈ s,
        0 ≤ affineFun (S e.2 - S e.1 - a e.1) (fun i => -(b e.1 i)) v :=
      fun v hv => (precedence_le_iff (S e.1) (S e.2) (a e.1) (b e.1) v).mp (h v hv e he)
    have hnonneg := (affineFun_nonneg_hull_iff s _ _).mpr hper x hx
    exact (precedence_le_iff (S e.1) (S e.2) (a e.1) (b e.1) x).mpr hnonneg

/-- Duration nonnegativity over the hull, checked separately at the
vertices, for every activity in `A`. -/
theorem durations_nonneg_hull_iff {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset (ι → ℝ)) (A : Finset J)
    (a : J → ℝ) (b : J → ι → ℝ) :
    (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), ∀ j ∈ A, 0 ≤ affineFun (a j) (b j) x)
      ↔ ∀ v ∈ s, ∀ j ∈ A, 0 ≤ affineFun (a j) (b j) v := by
  constructor
  · intro h v hv j hj
    exact h v (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)) j hj
  · intro h x hx j hj
    exact (affineFun_nonneg_hull_iff s (a j) (b j)).mpr (fun v hv => h v hv j hj) x hx

end AffineVertex
