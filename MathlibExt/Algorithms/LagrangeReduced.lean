/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lagrange-reduced pairs

A Lagrange-reduced pair of lattice vectors `u, v` (size-reduced, `|u ⬝ᵥ v| ≤ u ⬝ᵥ u / 2`,
and ordered, `u ⬝ᵥ u ≤ v ⬝ᵥ v`) has the squared length of `u` within a factor `4 / 3` of
that of every nonzero integer combination. The LLL algorithm is not included here.
-/

@[expose] public section

namespace MathlibExt.Algorithms.LagrangeReduced

private theorem dotProduct_expand {n : ℕ} (u v : Fin n → ℝ) (A B : ℝ) :
    (fun i => A * u i + B * v i) ⬝ᵥ (fun i => A * u i + B * v i)
      = A ^ 2 * (u ⬝ᵥ u) + 2 * A * B * (u ⬝ᵥ v) + B ^ 2 * (v ⬝ᵥ v) := by
  unfold dotProduct
  have hexp : ∀ i : Fin n,
      (A * u i + B * v i) * (A * u i + B * v i)
        = A ^ 2 * (u i * u i) + (2 * A * B) * (u i * v i) + B ^ 2 * (v i * v i) := by
    intro i
    ring
  simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem one_le_sq_int_cast {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have h2 : (1 : ℝ) ≤ |(z : ℝ)| ^ 2 := by nlinarith [h1, sq_nonneg (|(z : ℝ)| - 1)]
  rwa [sq_abs] at h2

/-- Lagrange-reduced pairs give near-shortest vectors. If `|u ⬝ᵥ v| ≤ u ⬝ᵥ u / 2` and
`u ⬝ᵥ u ≤ v ⬝ᵥ v`, then every nonzero integer combination of `u` and `v` has squared
length at least `(3 / 4) (u ⬝ᵥ u)`: in squared length, `u` is within a factor `4 / 3` of
the shortest vector of the lattice it spans with `v`. -/
theorem lagrange_short {n : ℕ} (u v : Fin n → ℝ)
    (hu : 0 < u ⬝ᵥ u)
    (hμ : |u ⬝ᵥ v| ≤ u ⬝ᵥ u / 2)
    (hle : u ⬝ᵥ u ≤ v ⬝ᵥ v)
    (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    u ⬝ᵥ u ≤ (4 / 3) * ((fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
      (fun i => (a : ℝ) * u i + (b : ℝ) * v i)) := by
  have hexp : (fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
        (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
      = (a : ℝ) ^ 2 * (u ⬝ᵥ u) + 2 * (a : ℝ) * (b : ℝ) * (u ⬝ᵥ v)
        + (b : ℝ) ^ 2 * (v ⬝ᵥ v) :=
    dotProduct_expand u v _ _
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun h => hab (by rw [h, hb])
    have hA2 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := one_le_sq_int_cast ha
    have hB0 : (b : ℝ) = 0 := by simp [hb]
    rw [hexp, hB0]
    norm_num
    nlinarith [hA2, hu, mul_nonneg (sub_nonneg.mpr hA2) hu.le]
  · have hB2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_sq_int_cast hb
    have hC2 : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u / 2) ^ 2 :=
      sq_le_sq' (abs_le.mp hμ).1 (abs_le.mp hμ).2
    have hDE : (u ⬝ᵥ u) * (u ⬝ᵥ u) ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) :=
      mul_le_mul_of_nonneg_left hle hu.le
    have hgap : 3 * (u ⬝ᵥ u) ^ 2 / 4 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
      nlinarith [hC2, hDE]
    have hident : (u ⬝ᵥ u) * ((fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i))
        = ((a : ℝ) * (u ⬝ᵥ u) + (b : ℝ) * (u ⬝ᵥ v)) ^ 2
          + (b : ℝ) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) := by
      rw [hexp]
      ring
    have hsq : (0 : ℝ) ≤ ((a : ℝ) * (u ⬝ᵥ u) + (b : ℝ) * (u ⬝ᵥ v)) ^ 2 := sq_nonneg _
    have hmul : (1 : ℝ) * (3 * (u ⬝ᵥ u) ^ 2 / 4)
        ≤ (b : ℝ) ^ 2 * ((u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2) :=
      mul_le_mul hB2 hgap (by positivity) (sq_nonneg _)
    have hDW : 3 * (u ⬝ᵥ u) ^ 2 / 4
        ≤ (u ⬝ᵥ u) * ((fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i)) := by
      rw [hident]
      linarith [hsq, hmul]
    have hW : 3 * (u ⬝ᵥ u) / 4
        ≤ (fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i) := by
      have hmul2 : (u ⬝ᵥ u) * (3 * (u ⬝ᵥ u) / 4)
          ≤ (u ⬝ᵥ u) * ((fun i => (a : ℝ) * u i + (b : ℝ) * v i) ⬝ᵥ
            (fun i => (a : ℝ) * u i + (b : ℝ) * v i)) := by
        have heq : (u ⬝ᵥ u) * (3 * (u ⬝ᵥ u) / 4) = 3 * (u ⬝ᵥ u) ^ 2 / 4 := by ring
        rw [heq]
        exact hDW
      exact le_of_mul_le_mul_left hmul2 hu
    linarith [hW]

end MathlibExt.Algorithms.LagrangeReduced

end
