/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-!
# First-order Taylor remainder for univariate polynomials

Over an arbitrary commutative ring, every polynomial agrees with its
first-order Taylor expansion at a point up to a multiple of the squared
monic divisor `(X - C a) ^ 2`, and the quotient is unique. Uniqueness is by
cancellation against the monic divisor, so no domain hypothesis is needed.
-/

/-- **First-order Taylor expansion of a polynomial.** Let $R$ be a commutative ring, let
$f \in R[X]$ and $a \in R$, and let $f'$ be the formal derivative of $f$. There is a unique
polynomial $g \in R[X]$ such that
$$f = f(a) + f'(a)\,(X - a) + g\,(X - a)^2.$$ -/
theorem existsUnique_taylor_remainder (f : R[X]) (a : R) :
    ∃! g : R[X],
      f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
        g * (X - C a) ^ 2 := by
  obtain ⟨q₁, hq₁⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := f)
  obtain ⟨g, hg⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := q₁)
  have hdecomp : f = C (f.eval a) + (X - C a) * q₁ := by
    linear_combination hq₁
  have hder : f.derivative = q₁ + (X - C a) * q₁.derivative := by
    have hcalc : (C (f.eval a) + (X - C a) * q₁).derivative =
        q₁ + (X - C a) * q₁.derivative := by
      rw [derivative_add, derivative_C, zero_add, derivative_mul,
        derivative_X_sub_C, one_mul]
    rwa [← hdecomp] at hcalc
  have hderiv : q₁.eval a = f.derivative.eval a := by
    have h := congrArg (eval a) hder
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      add_zero] at h
    exact h.symm
  have hq₂eq : q₁ = C (f.derivative.eval a) + (X - C a) * g := by
    rw [← hderiv]
    linear_combination hg
  have key : f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
      g * (X - C a) ^ 2 := by
    calc f = C (f.eval a) + (X - C a) * q₁ := hdecomp
      _ = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
          g * (X - C a) ^ 2 := by
        rw [hq₂eq]
        ring
  refine ⟨g, key, ?_⟩
  intro y hy
  have hcancel : (y - g) * (X - C a) ^ 2 = 0 := by
    linear_combination key - hy
  exact sub_eq_zero.mp (((monic_X_sub_C a).pow 2).mul_left_eq_zero_iff.mp hcancel)

end Polynomial
