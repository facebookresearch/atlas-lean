/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binet formulas for Fibonacci and Lucas polynomials

Let `α` be the formal root of `T ^ 2 - X * T - 1` over `ℤ[X]` and let `β = X - α`.
For every natural index, the Lucas polynomial is the sum of the two root powers, and the
Fibonacci polynomial multiplied by `α - β` is their difference. These identities do not
require division by `α - β`.

## References

* Thomas Koshy, *Fibonacci and Lucas Numbers with Applications*, vol. 2,
  John Wiley & Sons, 2019 (Binet formulas, as cited by Lin and Zhou in §2).
* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, §2.
* The Lean proofs of the root identities and Binet formulas were first used in
  `MathlibExt.NumberTheory.FibonacciPolynomialOddPowerSub`.
-/

namespace MetaMathlibExt.FibonacciPolynomialBinet

open Polynomial
open scoped QuadraticAlgebra

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1
local notation "A" => QuadraticAlgebra ℤ[X] (1 : ℤ[X]) X
local notation "ι" => algebraMap ℤ[X] A
local notation "α" => (QuadraticAlgebra.omega : A)
local notation "β" => (ι X - α)

private theorem root_sq : α ^ 2 = ι X * α + 1 := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_one, add_comm]

private theorem other_root_sq : β ^ 2 = ι X * β + 1 := by
  linear_combination root_sq

/-- In the quadratic algebra over `ℤ[X]` with `α² = Xα + 1`, the product of `α` and `X - α`
is `-1`, the constant coefficient of `T² - XT - 1`. -/
public theorem root_mul_other : α * β = -1 := by
  linear_combination -root_sq

/-- In the quadratic algebra over `ℤ[X]` with `α² = Xα + 1`, the squared difference of `α`
and `X - α` is the discriminant `X² + 4`. -/
public theorem root_diff_sq : (α - β) ^ 2 = ι (X ^ 2 + 4) := by
  rw [map_add, map_pow, map_ofNat]
  linear_combination 4 * root_sq

private theorem root_power_rec (u : A) (hu : u ^ 2 = ι X * u + 1) (r : ℕ) :
    u ^ (r + 2) = ι X * u ^ (r + 1) + u ^ r := by
  rw [pow_add u r 2, pow_add u r 1, hu, pow_one]
  ring

/-- The division-free Binet formula for Fibonacci polynomials: for every natural index `r`,
`(α - β) f_r = α^r - β^r` in the quadratic algebra over `ℤ[X]` with `α² = Xα + 1`
and `β = X - α`. Here `f_0 = 0`, `f_1 = 1`, and `f_{r+2} = X f_{r+1} + f_r`. -/
public theorem fib_binet (r : ℕ) : (α - β) * ι (𝔣 r) = α ^ r - β ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more r h₀ h₁ =>
    rw [generalizedFibonacciPolynomial_add_two, one_mul, map_add, map_mul,
      root_power_rec α root_sq, root_power_rec β other_root_sq]
    linear_combination h₀ + ι X * h₁

/-- The Binet formula for Lucas polynomials: for every natural index `r`, `ℓ_r = α^r + β^r`
in the quadratic algebra over `ℤ[X]` with `α² = Xα + 1` and `β = X - α`.
Here `ℓ_0 = 2`, `ℓ_1 = X`, and `ℓ_{r+2} = X ℓ_{r+1} + ℓ_r`. -/
public theorem lucas_binet (r : ℕ) : ι (𝔩 r) = α ^ r + β ^ r := by
  induction r using Nat.twoStepInduction with
  | zero => norm_num [map_ofNat]
  | one => simp
  | more r h₀ h₁ =>
    rw [generalizedFibonacciPolynomial_add_two, one_mul, map_add, map_mul, h₀, h₁,
      root_power_rec α root_sq, root_power_rec β other_root_sq]
    ring

end MetaMathlibExt.FibonacciPolynomialBinet
