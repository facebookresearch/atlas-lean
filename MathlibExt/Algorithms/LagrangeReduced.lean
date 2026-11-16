/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lagrange-reduced pairs

A size-reduced pair of lattice vectors has its first
vector within a factor `4 / 3` of every nonzero integer
combination. The LLL algorithm is not included here.
-/

@[expose] public section

/-- Dot product of real vectors. -/
noncomputable def vdot {n : ℕ} (u v : Fin n → ℝ) : ℝ :=
  ∑ i, u i * v i

private theorem vdot_expand {n : ℕ} (u v : Fin n → ℝ) (A B : ℝ) :
    vdot (fun i => A * u i + B * v i) (fun i => A * u i + B * v i)
      = A ^ 2 * vdot u u + 2 * A * B * vdot u v + B ^ 2 * vdot v v := by
  unfold vdot
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

/-- Lagrange-reduced pairs give near-shortest vectors
(ALG-54 core). If `|⟨u, v⟩| ≤ ⟨u, u⟩ / 2` and
`⟨u, u⟩ ≤ ⟨v, v⟩`, then every nonzero integer combination
of `u` and `v` has squared length at least
`(3 / 4) ⟨u, u⟩`: `u` is within a factor `4 / 3` of the
shortest vector of the lattice it spans with `v`. -/
theorem lagrange_short {n : ℕ} (u v : Fin n → ℝ)
    (hu : 0 < vdot u u)
    (hμ : |vdot u v| ≤ vdot u u / 2)
    (hle : vdot u u ≤ vdot v v)
    (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    vdot u u ≤ (4 / 3) * vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
      (fun i => (a : ℝ) * u i + (b : ℝ) * v i) := by
  have hexp : vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
        (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
      = (a : ℝ) ^ 2 * vdot u u + 2 * (a : ℝ) * (b : ℝ) * vdot u v
        + (b : ℝ) ^ 2 * vdot v v :=
    vdot_expand u v _ _
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun h => hab (by rw [h, hb])
    have hA2 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := one_le_sq_int_cast ha
    have hB0 : (b : ℝ) = 0 := by simp [hb]
    rw [hexp, hB0]
    norm_num
    nlinarith [hA2, hu, mul_nonneg (sub_nonneg.mpr hA2) hu.le]
  · have hB2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := one_le_sq_int_cast hb
    have hC2 : (vdot u v) ^ 2 ≤ (vdot u u / 2) ^ 2 :=
      sq_le_sq' (abs_le.mp hμ).1 (abs_le.mp hμ).2
    have hDE : vdot u u * vdot u u ≤ vdot u u * vdot v v :=
      mul_le_mul_of_nonneg_left hle hu.le
    have hgap : 3 * (vdot u u) ^ 2 / 4 ≤ vdot u u * vdot v v - (vdot u v) ^ 2 := by
      nlinarith [hC2, hDE]
    have hident : vdot u u * vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
        = ((a : ℝ) * vdot u u + (b : ℝ) * vdot u v) ^ 2
          + (b : ℝ) ^ 2 * (vdot u u * vdot v v - (vdot u v) ^ 2) := by
      rw [hexp]
      ring
    have hsq : (0 : ℝ) ≤ ((a : ℝ) * vdot u u + (b : ℝ) * vdot u v) ^ 2 := sq_nonneg _
    have hmul : (1 : ℝ) * (3 * (vdot u u) ^ 2 / 4)
        ≤ (b : ℝ) ^ 2 * (vdot u u * vdot v v - (vdot u v) ^ 2) :=
      mul_le_mul hB2 hgap (by positivity) (sq_nonneg _)
    have hDW : 3 * (vdot u u) ^ 2 / 4
        ≤ vdot u u * vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i) := by
      rw [hident]
      linarith [hsq, hmul]
    have hW : 3 * vdot u u / 4
        ≤ vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
          (fun i => (a : ℝ) * u i + (b : ℝ) * v i) := by
      have hmul2 : vdot u u * (3 * vdot u u / 4)
          ≤ vdot u u * vdot (fun i => (a : ℝ) * u i + (b : ℝ) * v i)
            (fun i => (a : ℝ) * u i + (b : ℝ) * v i) := by
        have heq : vdot u u * (3 * vdot u u / 4) = 3 * (vdot u u) ^ 2 / 4 := by ring
        rw [heq]
        exact hDW
      exact le_of_mul_le_mul_left hmul2 hu
    linarith [hW]

end
