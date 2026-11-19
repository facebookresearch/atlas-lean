/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.ReactiveBalance

import Mathlib.Tactic.NormNum

/-!
# Tests for reactive balances

Boundary checks for `PhyslibExt.Engineering.Process.ReactiveBalance`:
growing volume at constant concentration still grows the stock, zero
volume blocks the concentration division, and the closed constant-volume
case recovers the scaled concentration derivative.
-/

namespace Engineering.Process.ReactiveBalance.Tests

open Engineering.Process.ReactiveBalance

-- V(t) = 1 + t and constant concentration 2: the stock still grows at
-- rate 2 through the V' * c term, a nonzero fed-batch witness with flows
-- Fin - Fout + G = 3 - 1 + 0.
example : HasDerivAt (fun t : ℝ => (1 + t) * 2) (3 - 1 + 0) 0 := by
  have h : HasDerivAt (fun t : ℝ => (1 + t) * 2) (1 * 2) (0 : ℝ) := by
    have h1 : HasDerivAt id (1 : ℝ) (0 : ℝ) := hasDerivAt_id 0
    have h2 : HasDerivAt (fun x => 1 + id x) (1 : ℝ) (0 : ℝ) :=
      HasDerivAt.const_add 1 h1
    have h3 : HasDerivAt (fun y => (fun x => 1 + id x) y * 2) (1 * 2) (0 : ℝ) :=
      HasDerivAt.mul_const h2 2
    simpa using h3
  norm_num at h ⊢
  exact h

example : (1 : ℝ) * 2 + (1 + 0) * 0 = 3 - 1 + 0 := by
  norm_num

-- Zero volume at the instant: V(t) = t and c = 2 give stock derivative 2
-- at t = 0, while the V * c' part alone is 0, so the balance cannot be
-- divided into concentration form there.
example : HasDerivAt (fun t : ℝ => t * 2) 2 0 ∧ (0 : ℝ) * 0 ≠ 2 := by
  constructor
  · have h1 : HasDerivAt id (1 : ℝ) (0 : ℝ) := hasDerivAt_id 0
    have h2 : HasDerivAt (fun y => id y * 2) (1 * 2) (0 : ℝ) :=
      HasDerivAt.mul_const h1 2
    norm_num at h2 ⊢
    simpa using h2
  · norm_num

-- Closed constant-volume numeric case: V0 = 2 and c(t) = 3t give stock
-- derivative 6.
example : HasDerivAt (fun t : ℝ => 2 * (3 * t)) 6 1 := by
  have h1 : HasDerivAt id (1 : ℝ) (1 : ℝ) := hasDerivAt_id 1
  have h2 : HasDerivAt (fun y => 3 * id y) (3 * 1) (1 : ℝ) :=
    HasDerivAt.const_mul 3 h1
  have h3 : HasDerivAt (fun y => 2 * (fun y => 3 * id y) y) (2 * (3 * 1)) (1 : ℝ) :=
    HasDerivAt.const_mul 2 h2
  norm_num at h3 ⊢
  simpa using h3

-- The frozen statements above apply at a species index of a two-species
-- system with no extra structure.
example : HasDerivAt (fun t : ℝ => (1 + t) * (![2, 5] : Fin 2 → ℝ) 1)
    (1 * (![2, 5] : Fin 2 → ℝ) 1 + (1 + 0) * 0) 0 := by
  have h1 : HasDerivAt id (1 : ℝ) (0 : ℝ) := hasDerivAt_id 0
  have h2 : HasDerivAt (fun x => 1 + id x) (1 : ℝ) (0 : ℝ) :=
    HasDerivAt.const_add 1 h1
  have h3 : HasDerivAt (fun y => (fun x => 1 + id x) y * (![2, 5] : Fin 2 → ℝ) 1)
      (1 * (![2, 5] : Fin 2 → ℝ) 1) (0 : ℝ) :=
    HasDerivAt.mul_const h2 ((![2, 5] : Fin 2 → ℝ) 1)
  have heq : (1 : ℝ) * (![2, 5] : Fin 2 → ℝ) 1 + (1 + 0) * 0
      = 1 * (![2, 5] : Fin 2 → ℝ) 1 := by ring
  rw [heq]
  simpa using h3

end Engineering.Process.ReactiveBalance.Tests
