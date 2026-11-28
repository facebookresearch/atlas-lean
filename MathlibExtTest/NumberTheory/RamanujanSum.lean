/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamanujanSum

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Ramanujan sums
-/

@[expose] public section

open MetaMathlibExt ArithmeticFunction
open scoped ArithmeticFunction.Moebius

example (n : ℕ) [NeZero n] : ramanujanSum n 0 = Nat.totient n := by
  simp

example (t : ℤ) : ramanujanSum 1 t = 1 := by
  simp

example : ramanujanSum 1 (-7) = 1 := by
  simp

example : ramanujanSum 2 1 = -1 := by
  have hcard : Fintype.card (ZMod 2)ˣ = 1 := by
    simp
  obtain ⟨u, hu⟩ := Fintype.card_eq_one_iff.mp hcard
  let _ : Unique (ZMod 2)ˣ := { default := u, uniq := hu }
  rw [ramanujanSum, Fintype.sum_unique]
  change ZMod.stdAddChar (u.val * (1 : ZMod 2)) = -1
  have hu_one : u = 1 := (hu u).trans (hu 1).symm
  rw [hu_one, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  norm_num [ZMod.cast, ZMod.val_one]
  rw [show 2 * (Real.pi : ℂ) * Complex.I / 2 = (Real.pi : ℂ) * Complex.I by ring]
  exact Complex.exp_pi_mul_I

example (n : ℕ) [NeZero n] (t k : ℤ) :
    ramanujanSum n (t + k * n) = ramanujanSum n t := by
  simp

/-! ### Evaluation through the Möbius function -/

-- `c_n(1) = μ(n)`: the previous hand computation of `c_2(1)` now follows by `simp`.
example : ramanujanSum 2 1 = -1 := by
  simp [moebius_apply_prime Nat.prime_two]

example : ramanujanSum 6 1 = 1 := by
  rw [ramanujanSum_one, show μ 6 = 1 by decide +kernel]
  simp

example : ramanujanSum 4 1 = 0 := by
  rw [ramanujanSum_one, show μ 4 = 0 by decide +kernel]
  simp

-- `c_4(2) = 1 · μ(4) + 2 · μ(2) = -2`.
example : ramanujanSum 4 2 = -2 := by
  rw [ramanujanSum_eq_sum_divisors_gcd, show Int.gcd 2 (4 : ℕ) = 2 by rfl,
    Nat.Prime.sum_divisors Nat.prime_two, show μ (4 / 1) = 0 by decide +kernel,
    show μ (4 / 2) = -1 by decide +kernel]
  norm_num

-- At `t = 0`, the divisor formula recovers `c_n(0) = φ(n)`, i.e. `∑_{d ∣ n} d μ(n/d) = φ(n)`.
example (n : ℕ) [NeZero n] :
    ∑ d ∈ n.divisors, (d : ℂ) * μ (n / d) = Nat.totient n := by
  have h := ramanujanSum_eq_sum_divisors_gcd n 0
  simp only [Int.gcd_zero_left, Int.natAbs_natCast, ramanujanSum_zero] at h
  exact h.symm

-- The classical exponential form at `n = 1`: a single term `h = 0`.
example (t : ℤ) : ramanujanSum 1 t =
    ∑ h ∈ Finset.range 1 with h.Coprime 1, Complex.exp (2 * Real.pi * Complex.I * h * t / ((1 : ℕ) : ℂ)) :=
  ramanujanSum_eq_sum_exp 1 t

example (n : ℕ) [NeZero n] (t : ℤ) : ramanujanSum n t =
    ∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℤ) ∣ t), (μ (n / d) : ℂ) * d :=
  ramanujanSum_eq_sum_divisors_moebius n t
