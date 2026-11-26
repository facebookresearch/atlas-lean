/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.InterpolationPolyExchange
import Mathlib.Tactic.Linarith

/-! # Tests for the exchange formula for interpolation polynomials -/

open MetaMathlibExt Polynomial

-- With no common nodes, the coefficient is the divided difference `(f a - f b) / (a - b)`.
example (a b : ℤ) (f : ℤ → ℤ) :
    (interpolationPoly {a, b} f).coeff 1 * ((a : ℚ) - b) = f a - f b := by
  have h := interpolationPoly_exchange ∅ (Finset.notMem_empty a) (Finset.notMem_empty b) f
  simp only [Finset.insert_empty, Finset.card_empty, zero_add, Finset.prod_empty,
    mul_one] at h
  have hs (x : ℤ) : interpolationPoly {x} f = C (f x : ℚ) := Lagrange.interpolate_singleton _
  have h0 := congrArg (Polynomial.eval 0) h
  simp only [hs, eval_add, eval_C] at h0
  linarith

-- If the top coefficient on `X ∪ {a, b}` vanishes, the two interpolants coincide.
example (X : Finset ℤ) {a b : ℤ} (ha : a ∉ X) (hb : b ∉ X) (f : ℤ → ℤ)
    (h : (interpolationPoly (insert a (insert b X)) f).degree ≤ X.card) :
    interpolationPoly (insert a X) f = interpolationPoly (insert b X) f := by
  rw [interpolationPoly_exchange X ha hb f,
    coeff_eq_zero_of_degree_lt (h.trans_lt (by exact_mod_cast Nat.lt_succ_self _)), zero_mul,
    C_0, zero_mul, add_zero]

-- Evaluating at `a` gives the error of `f_{X ∪ {b}}` at the node `a`.
example (X : Finset ℤ) {a b : ℤ} (ha : a ∉ X) (hb : b ∉ X) (f : ℤ → ℤ) :
    (f a : ℚ) = (interpolationPoly (insert b X) f).eval (a : ℚ) +
      (interpolationPoly (insert a (insert b X)) f).coeff (X.card + 1) * ((a : ℚ) - b) *
        ∏ z ∈ X, ((a : ℚ) - z) := by
  have h := congrArg (Polynomial.eval (a : ℚ)) (interpolationPoly_exchange X ha hb f)
  rw [eval_interpolationPoly f (Finset.mem_insert_self a X)] at h
  simpa [eval_prod] using h

-- For `f(x) = x²` the coefficient of `x²` on the three nodes `1, 2, 0` is `1`, so the secant
-- lines of `f` through `1, 0` and through `2, 0` differ by `(1 - 2) x`.
example : interpolationPoly {1, 0} (fun x => x ^ 2) =
    interpolationPoly {2, 0} (fun x => x ^ 2) - Polynomial.X := by
  have hsq : interpolationPoly {1, 2, 0} (fun x => x ^ 2) = Polynomial.X ^ 2 := by
    symm
    refine Lagrange.eq_interpolate_of_eval_eq _ (fun _ _ _ _ h => Int.cast_injective h) ?_ ?_
    · rw [degree_X_pow]
      decide
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> norm_num
  have h := interpolationPoly_exchange {0} (a := 1) (b := 2) (by decide) (by decide)
    (fun x => x ^ 2)
  rw [hsq] at h
  norm_num at h
  rw [h]
  ring
