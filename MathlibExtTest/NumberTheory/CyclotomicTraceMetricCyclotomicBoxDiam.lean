/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicTraceMetricCyclotomicBoxDiam
import Mathlib.Tactic.NormNum

/-! # Tests for the diameter of the cyclotomic box -/

namespace MathlibExtTest.NumberTheory.CyclotomicTraceMetricCyclotomicBoxDiam

open MetaMathlibExt IsCyclotomicExtension

variable {K : Type*} [Field K] [CharZero K]

-- At conductor three and radius one the attained bound is `6 * √2`.
example [IsCyclotomicExtension {3} ℚ K] :
    cyclotomicTraceDist 3
        (cyclotomicLatticePoint K fun i : Fin (3 - 1) => (1 : ℤ) * (-1) ^ i.val)
        (cyclotomicLatticePoint K fun i : Fin (3 - 1) => -((1 : ℤ) * (-1) ^ i.val)) =
      6 * √(2 : ℝ) := by
  have h := (cyclotomicBox_diam (K := K) Nat.prime_three (by decide) 1).2
  convert h using 3 <;> norm_num

-- In the radius-zero box every trace distance vanishes.
example {p : ℕ} [NeZero p] [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) (hp2 : p ≠ 2)
    (a b : Fin (p - 1) → ℤ) (ha : a ∈ cyclotomicBox p 0) (hb : b ∈ cyclotomicBox p 0) :
    cyclotomicTraceDist p (cyclotomicLatticePoint K a) (cyclotomicLatticePoint K b) = 0 := by
  have hle := (cyclotomicBox_diam (K := K) hp hp2 0).1 a ha b hb
  have hle0 : cyclotomicTraceDist p (cyclotomicLatticePoint K a)
      (cyclotomicLatticePoint K b) ≤ 0 := by
    simpa using hle
  have hnonneg : (0 : ℝ) ≤ cyclotomicTraceDist p (cyclotomicLatticePoint K a)
      (cyclotomicLatticePoint K b) := by
    simp [cyclotomicTraceDist, cyclotomicTraceNorm]
  exact le_antisymm hle0 hnonneg

-- At conductor three and radius one opposite constant vectors are within `6 * √2`.
example [IsCyclotomicExtension {3} ℚ K] :
    cyclotomicTraceDist 3 (cyclotomicLatticePoint K fun _ : Fin (3 - 1) => (1 : ℤ))
        (cyclotomicLatticePoint K fun _ : Fin (3 - 1) => (-1 : ℤ)) ≤ 6 * √(2 : ℝ) := by
  have ha : (fun _ : Fin (3 - 1) => (1 : ℤ)) ∈ cyclotomicBox 3 1 := by decide
  have hb : (fun _ : Fin (3 - 1) => (-1 : ℤ)) ∈ cyclotomicBox 3 1 := by decide
  have hle := (cyclotomicBox_diam (K := K) Nat.prime_three (by decide) 1).1 _ ha _ hb
  convert hle using 2 <;> norm_num

end MathlibExtTest.NumberTheory.CyclotomicTraceMetricCyclotomicBoxDiam
