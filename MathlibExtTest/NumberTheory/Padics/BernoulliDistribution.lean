/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.BernoulliDistribution

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic.NormNum

/-!
# Tests for the Bernoulli distributions on `ℤ_[p]`
-/

@[expose] public section

open MetaMathlibExt

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### The multiplication formula for Bernoulli polynomials -/

example (m n : ℕ) (x : ℚ) :
    (m : ℚ) ^ n * ∑ b ∈ Finset.range m, (Polynomial.bernoulli n).eval (x + b / m) =
      m * (Polynomial.bernoulli n).eval (m * x) :=
  Polynomial.pow_mul_sum_bernoulli_eval_add_div m n x

/-- `m = 2`, `n = 1`: `2 (B_1(x) + B_1(x + 1/2)) = 2 B_1(2 x)`, checked by hand. -/
example (x : ℚ) : (Polynomial.bernoulli 1).eval x + (Polynomial.bernoulli 1).eval (x + 1 / 2) =
    (Polynomial.bernoulli 1).eval (2 * x) := by
  simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  ring

/-- The formula holds at `m = 0` with no hypothesis (both sides vanish). -/
example (n : ℕ) (x : ℚ) :
    ((0 : ℕ) : ℚ) ^ n * ∑ b ∈ Finset.range 0, (Polynomial.bernoulli n).eval (x + b / (0 : ℕ)) =
      ((0 : ℕ) : ℚ) * (Polynomial.bernoulli n).eval (((0 : ℕ) : ℚ) * x) :=
  Polynomial.pow_mul_sum_bernoulli_eval_add_div 0 n x

/-! ### `bernoulliDist`: values and the `B_1` convention -/

/-- At level `0` the whole of `ℤ_[p]` has mass the Bernoulli number `B_k`. -/
example (p k : ℕ) [Fact p.Prime] : bernoulliDist p k 0 0 = (bernoulli k : ℚ_[p]) := by
  simp [bernoulliDist, Polynomial.bernoulli_eval_zero]

/-- `μ_1(ℤ_[p]) = B_1 = -1/2` (Mathlib's convention, `B_1(x) = x - 1/2`). -/
example : bernoulliDist 3 1 0 0 = (-1 / 2 : ℚ_[3]) := by
  simp [bernoulliDist, Polynomial.bernoulli_one]
  norm_num

/-- `μ_1(1 + 3 ℤ_[3]) = B_1(1/3) = 1/3 - 1/2 = -1/6`. -/
example : bernoulliDist 3 1 1 1 = (-1 / 6 : ℚ_[3]) := by
  simp [bernoulliDist, Polynomial.bernoulli_one]
  norm_num

/-- `μ_1(2 + 3 ℤ_[3]) = B_1(2/3) = 1/6`. -/
example : bernoulliDist 3 1 1 2 = (1 / 6 : ℚ_[3]) := by
  simp [bernoulliDist, Polynomial.bernoulli_one]
  norm_num

/-- `μ_2(1 + 3 ℤ_[3]) = 3 B_2(1/3) = 3 (1/9 - 1/3 + 1/6) = -1/6`. -/
example : bernoulliDist 3 2 1 1 = (-1 / 6 : ℚ_[3]) := by
  simp [bernoulliDist, Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_two]
  norm_num

/-- `μ_0` is the (unbounded) Haar distribution: `μ_0(a + p ^ N ℤ_[p]) = p ^ (-N)`. -/
example (p N a : ℕ) [Fact p.Prime] :
    bernoulliDist p 0 N a = ((p : ℚ) ^ (-(N : ℤ)) : ℚ) := by
  simp [bernoulliDist]

/-! ### `IsPadicDistribution` and `IsBoundedPadicDistribution` -/

/-- The zero family is a bounded distribution. -/
example (p : ℕ) [Fact p.Prime] : IsBoundedPadicDistribution p (fun _ _ => 0) :=
  ⟨fun _ _ _ => by simp, 0, fun _ _ _ => by simp⟩

/-- A non-example: the constant family `1` violates the distribution relation (`1 ≠ p`). -/
example (p : ℕ) [Fact p.Prime] : ¬ IsPadicDistribution p (fun _ _ => 1) := by
  intro h
  have h1 := h 0 0 (by simp)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  have h2 : ((1 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) := by simpa using h1
  have := (Fact.out : p.Prime).one_lt
  exact absurd (Nat.cast_injective h2) (by omega)

/-- The predicate only constrains `μ N a` for `a < p ^ N`: junk values outside this range are
free. -/
example (p : ℕ) [Fact p.Prime] :
    IsPadicDistribution p (fun N a => if a < p ^ N then 0 else 1) := by
  intro N a ha
  have hp := (Fact.out : p.Prime).pos
  have hlt : ∀ b ∈ Finset.range p, a + b * p ^ N < p ^ (N + 1) := by
    intro b hb
    have hb' := Finset.mem_range.mp hb
    calc a + b * p ^ N < p ^ N + b * p ^ N := by omega
      _ = (b + 1) * p ^ N := by ring
      _ ≤ p * p ^ N := Nat.mul_le_mul_right _ hb'
      _ = p ^ (N + 1) := by ring
  simp only [ha, ↓reduceIte]
  exact (Finset.sum_eq_zero fun b hb => by simp [hlt b hb]).symm

/-- `μ_k` is a distribution for every `k`. -/
example : IsPadicDistribution 5 (bernoulliDist 5 3) :=
  bernoulliDist_isPadicDistribution 5 3

/-- The distribution relation for `μ_1` at level `0`, checked by hand:
`B_1(0) = B_1(0) + B_1(1/3) + B_1(2/3)`, i.e. `-1/2 = -1/2 - 1/6 + 1/6`. -/
example : bernoulliDist 3 1 0 0 =
    bernoulliDist 3 1 1 0 + bernoulliDist 3 1 1 1 + bernoulliDist 3 1 1 2 := by
  simp [bernoulliDist, Polynomial.bernoulli_one]
  norm_num

/-- `μ_0` is a distribution but not a measure: its ball values `p ^ (-N)` are unbounded. -/
example : IsPadicDistribution 2 (bernoulliDist 2 0) ∧
    ¬ IsBoundedPadicDistribution 2 (bernoulliDist 2 0) := by
  refine ⟨bernoulliDist_isPadicDistribution 2 0, fun ⟨_, B, hB⟩ => ?_⟩
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 2)
  have h := hB N 0 (by positivity)
  have hv : bernoulliDist 2 0 N 0 = (2 : ℚ_[2]) ^ (-(N : ℤ)) := by
    simp [bernoulliDist]
  rw [hv] at h
  have hn : ‖(2 : ℚ_[2]) ^ (-(N : ℤ))‖ = (2 : ℝ) ^ N := by
    have := Padic.norm_p_zpow (p := 2) (-(N : ℤ))
    push_cast at this
    rw [this, neg_neg, zpow_natCast]
  rw [hn] at h
  linarith

/-! ### The regularised distributions and the Mazur measure -/

/-- `μ_{1,2}(1 + 3 ℤ_[3]) = μ_1(1 + 3ℤ_[3]) - 2⁻¹ μ_1(2 + 3ℤ_[3]) = -1/6 - 1/12 = -1/4`,
directly from the definition. -/
example : regBernoulliDist 3 1 2 1 1 = (-1 / 4 : ℚ_[3]) := by
  have h : ((2 * ((1 : ℕ) : ℤ)) % (3 : ℤ) ^ 1).toNat = 2 := by decide
  simp only [regBernoulliDist, Nat.cast_ofNat, h]
  simp [bernoulliDist, Polynomial.bernoulli_one]
  norm_num

/-- The same value from the closed form `(2 ⌊α a / p ^ N⌋ + 1 - α) / (2 α)`. -/
example : regBernoulliDist 3 1 2 1 1 = (-1 / 4 : ℚ_[3]) := by
  rw [regBernoulliDist_one_eq 3 (by norm_num)]
  norm_num

/-- Closed form for a negative regulariser `α = -1` at `p = 5`:
`μ_{1,-1}(2 + 5 ℤ_[5]) = (2 ⌊-2/5⌋ + 2) / (-2) = 0`. -/
example : regBernoulliDist 5 1 (-1) 1 2 = 0 := by
  rw [regBernoulliDist_one_eq 5 (by norm_num)]
  norm_num

/-- The Mazur distribution is a measure. -/
example : IsBoundedPadicDistribution 3 (regBernoulliDist 3 1 2) :=
  regBernoulliDist_one_isBoundedPadicDistribution 3 (by norm_num [Int.isCoprime_iff_gcd_eq_one])

/-- At `p = 2` the Mazur distribution is still bounded by `1` (the factor `2` in the denominator is
absorbed because `α` is odd). -/
example (N a : ℕ) : ‖regBernoulliDist 2 1 3 N a‖ ≤ 1 :=
  norm_regBernoulliDist_one_le 2 (by norm_num [Int.isCoprime_iff_gcd_eq_one]) N a

/-- `μ_{2,2}(ℤ_[3]ˣ) = (1 - 2⁻²)(1 - 3) B_2 = -1/4`. -/
example : ∑ a ∈ Finset.Icc 1 (3 - 1), regBernoulliDist 3 2 2 1 a = (-1 / 4 : ℚ_[3]) := by
  rw [sum_regBernoulliDist_units_eq 3 (by norm_num [Int.isCoprime_iff_gcd_eq_one]) 2]
  simp [bernoulli_two]
  norm_num

/-- `μ_{1,α}(ℤ_[p]ˣ) = 0`, since the factor `1 - p ^ 0` vanishes. -/
example : ∑ a ∈ Finset.Icc 1 (5 - 1), regBernoulliDist 5 1 2 1 a = 0 := by
  rw [sum_regBernoulliDist_units_eq 5 (by norm_num [Int.isCoprime_iff_gcd_eq_one]) 1]
  simp

/-! ### The Kummer-type congruence -/

/-- `d = 6` clears the denominators of `B_2(x) = x ^ 2 - x + 1/6`, so the congruence applies. -/
example (N a : ℕ) :
    ‖(6 : ℚ_[5]) * regBernoulliDist 5 2 2 N a -
        (6 : ℚ_[5]) * (2 : ℚ_[5]) * (a : ℚ_[5]) ^ (2 - 1) * regBernoulliDist 5 1 2 N a‖ ≤
      (5 : ℝ) ^ (-(N : ℤ)) := by
  have hd : ∀ j ≤ 2, ((Polynomial.bernoulli 2).coeff j).den ∣ 6 := by
    intro j hj
    interval_cases j <;>
      simp [Polynomial.coeff_bernoulli, bernoulli_two, bernoulli_one]
  have := norm_regBernoulliDist_sub_mul_regBernoulliDist_one_le 5 (α := 2)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num) hd N a
  exact_mod_cast this

/-- The denominator hypothesis is also met by `d = 0`, for which the congruence is trivial. -/
example (k : ℕ) : ∀ j ≤ k, ((Polynomial.bernoulli k).coeff j).den ∣ 0 :=
  fun _ _ => dvd_zero _
