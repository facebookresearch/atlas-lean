/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample

/-! # Integer values and monotonicity of Campbell's interpolation -/

open MetaMathlibExt

-- The last integer on the exponential branch still lies strictly between zero and one.
example : 0 < campbellF 9 ∧ campbellF 9 < 1 := by
  constructor
  · rw [campbellF, ite_eq_left (by norm_num : (9 : ℝ) ≤ 100 / 11)]
    positivity
  · have h := floor_campbellF_eq_campbellH2.1 9 (by decide)
    rw [campbellH2_small.1, Nat.cast_ofNat, Nat.floor_eq_zero] at h
    exact h

-- Ten is the right endpoint of the initial linear branch.
example : campbellF 10 = 10 := by
  simpa [campbellH2_small.2.1] using floor_campbellF_eq_campbellH2.2 10 le_rfl

-- At a change of decade the new block starts with its own initial value.
example : campbellF 99 = 900 ∧ campbellF 100 = 1000 := by
  constructor
  · simpa [campbellH2_small.2.2.2.1] using floor_campbellF_eq_campbellH2.2 99 (by decide)
  · simpa [campbellH2_small.2.2.2.2] using floor_campbellF_eq_campbellH2.2 100 (by decide)

-- On the integral branch between `99` and `100` the interpolation stays between the values of
-- the sequence at the two integers.
example (x : ℝ) (h₁ : 99 ≤ x) (h₂ : x ≤ 100) : 900 ≤ campbellF x ∧ campbellF x ≤ 1000 := by
  have h99 : campbellF 99 = 900 := by
    simpa [campbellH2_small.2.2.2.1] using floor_campbellF_eq_campbellH2.2 99 (by decide)
  have h100 : campbellF 100 = 1000 := by
    simpa [campbellH2_small.2.2.2.2] using floor_campbellF_eq_campbellH2.2 100 (by decide)
  have hx : x ∈ Set.Ici 0 := Set.mem_Ici.2 (by linarith)
  constructor
  · rw [← h99]
    exact campbellF_monotoneOn (Set.mem_Ici.2 (by norm_num)) hx h₁
  · rw [← h100]
    exact campbellF_monotoneOn hx (Set.mem_Ici.2 (by norm_num)) h₂

-- Through the floor, monotonicity passes to Campbell's sequence from its first term on.
example {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : campbellH2 m ≤ campbellH2 n := by
  rw [← floor_campbellF_eq_campbellH2.1 m hm, ← floor_campbellF_eq_campbellH2.1 n (hm.trans hmn)]
  exact Nat.floor_le_floor (campbellF_monotoneOn (Set.mem_Ici.2 (Nat.cast_nonneg m))
    (Set.mem_Ici.2 (Nat.cast_nonneg n)) (by exact_mod_cast hmn))
