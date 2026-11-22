/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.DoubleRoot

public import Mathlib.Data.ZMod.Basic

namespace MathlibExtTest.Algebra.Polynomial.DoubleRoot

@[expose] public section

open _root_.Polynomial

/-- The iff applies to a polynomial over a general commutative ring. -/
public theorem test_iff {R : Type*} [CommRing R] (f : R[X]) (a : R) :
    f.eval a = 0 ∧ f.derivative.eval a = 0 ↔
      ∃ g : R[X], f = (X - C a) ^ 2 * g :=
  eval_and_derivative_eval_eq_zero_iff f a

/-- `(X - C a) ^ 2` itself has a double root at `a`. -/
public theorem test_sq_is_double_root {R : Type*} [CommRing R] (a : R) :
    ((X - C a) ^ 2 : R[X]).eval a = 0 ∧
      (((X - C a) ^ 2 : R[X]).derivative.eval a = 0) := by
  rw [← sq_dvd_iff_eval_and_derivative_eval_eq_zero]

/-- `X ^ 2` over `ℤ` has a double root at `0`. -/
public theorem test_X_sq_double_root_at_zero :
    ((X : ℤ[X]) ^ 2).eval 0 = 0 ∧ ((X : ℤ[X]) ^ 2).derivative.eval 0 = 0 := by
  rw [← sq_dvd_iff_eval_and_derivative_eval_eq_zero]
  exact ⟨1, by simp⟩

/-- The zero polynomial has a double root everywhere, including over a
ring with zero divisors: no domain hypothesis is used. -/
public theorem test_zero_double_root {R : Type*} [CommRing R] (a : R) :
    (0 : R[X]).eval a = 0 ∧ (0 : R[X]).derivative.eval a = 0 :=
  (sq_dvd_iff_eval_and_derivative_eval_eq_zero (0 : R[X]) a).mp
    ⟨0, by simp⟩

/-- The nonzero derivative of `X - C 3` excludes `(X - C 3) ^ 2`
as a factor. -/
public theorem test_simple_root :
    ¬ ((X - C (3 : ℤ)) ^ 2 : ℤ[X]) ∣ (X - C (3 : ℤ)) := by
  apply not_sq_dvd_of_derivative_eval_ne_zero
  simp

/-- Over `ZMod 4`, `(X - C 2) ^ 2` still has a double root at `2`,
although `ZMod 4` is not a domain. -/
public theorem test_sq_double_root_zmod4 :
    (((X - C (2 : ZMod 4)) ^ 2 : (ZMod 4)[X]).eval 2 = 0 ∧
      (((X - C (2 : ZMod 4)) ^ 2 : (ZMod 4)[X]).derivative.eval 2 = 0)) := by
  rw [← sq_dvd_iff_eval_and_derivative_eval_eq_zero]

end

end MathlibExtTest.Algebra.Polynomial.DoubleRoot
