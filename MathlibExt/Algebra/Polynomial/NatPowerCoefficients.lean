/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient separation from actual natural-parameter evaluations

Native polynomial root finiteness separates finite rational power sums.
The native separating algebraic dual transfers that separation to every
rational module. A multiplicative natural-parameter polynomial family in a
rational algebra therefore has orthogonal coefficient elements. The composition hypothesis is an ordinary polynomial identity.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u

namespace Polynomial

/-- The actual finite polynomial with its original coefficient index. -/
def finitePowerPolynomial (N : ℕ) (a : Fin N → ℚ) : Polynomial ℚ :=
  ∑ i : Fin N, monomial i.val (a i)

/-- Each original finite coefficient is recovered from the actual polynomial. -/
theorem finitePowerPolynomial_coeff (N : ℕ) (a : Fin N → ℚ) (i : Fin N) :
    (finitePowerPolynomial N a).coeff i.val = a i := by
  classical
  simp only [finitePowerPolynomial, finsetSum_coeff, coeff_monomial,
    ← Fin.ext_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The actual polynomial evaluation is the original finite rational power sum. -/
theorem finitePowerPolynomial_eval (N : ℕ) (a : Fin N → ℚ) (x : ℚ) :
    (finitePowerPolynomial N a).eval x = ∑ i : Fin N, a i * x ^ i.val := by
  simp only [finitePowerPolynomial, eval_finsetSum, eval_monomial]

/-- Equality at all actual natural rational values separates the actual finite scalar coefficients. -/
theorem finitePowerPolynomial_coefficients_eq (N : ℕ) (a b : Fin N → ℚ)
    (h : ∀ m : ℕ, (∑ i : Fin N, a i * (m : ℚ) ^ i.val) =
      ∑ i : Fin N, b i * (m : ℚ) ^ i.val) : a = b := by
  have hp : finitePowerPolynomial N a = finitePowerPolynomial N b := by
    apply eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.range (fun m : ℕ => (m : ℚ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply hi.mono
    rintro x ⟨m, rfl⟩
    change (finitePowerPolynomial N a).eval (m : ℚ) = (finitePowerPolynomial N b).eval (m : ℚ)
    simpa only [finitePowerPolynomial_eval] using h m
  funext i
  simpa only [finitePowerPolynomial_coeff] using congrArg (fun p => p.coeff i.val) hp

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The actual finite rational power combination in an arbitrary original rational module. -/
def finitePowerCombination (N : ℕ) (a : Fin N → V) (x : ℚ) : V :=
  ∑ i : Fin N, x ^ i.val • a i

/-- Native dual separation earns coefficient equality in every original rational module. -/
theorem finitePowerCombination_coefficients_eq (N : ℕ) (a b : Fin N → V)
    (h : ∀ m : ℕ, finitePowerCombination N a (m : ℚ) = finitePowerCombination N b (m : ℚ)) :
    a = b := by
  funext i
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ (a i - b i)).mp
  intro φ
  have hc : (fun j => φ (a j)) = fun j => φ (b j) := by
    apply finitePowerPolynomial_coefficients_eq
    intro m
    have hm := congrArg φ (h m)
    simpa only [finitePowerCombination, map_sum, map_smul, smul_eq_mul, mul_comm] using hm
  rw [map_sub, congrFun hc i, sub_self]

end Polynomial

namespace Algebra

variable {R : Type u} [Ring R] [Algebra ℚ R]

/-- The actual multiplicative polynomial-family identity forces orthogonality of its original coefficients. -/
theorem finitePowerCombination_coefficients_mul (N : ℕ) (e : Fin N → R)
    (h : ∀ a b : ℕ,
      Polynomial.finitePowerCombination N e (a : ℚ) * Polynomial.finitePowerCombination N e (b : ℚ) =
        Polynomial.finitePowerCombination N e ((a * b : ℕ) : ℚ)) :
    ∀ i j : Fin N, e i * e j = if i = j then e i else 0 := by
  classical
  have heigen (b : ℕ) :
      (fun i => e i * Polynomial.finitePowerCombination N e (b : ℚ)) =
        fun i => (b : ℚ) ^ i.val • e i := by
    apply Polynomial.finitePowerCombination_coefficients_eq
    intro a
    change (∑ i : Fin N, (a : ℚ) ^ i.val •
        (e i * Polynomial.finitePowerCombination N e (b : ℚ))) = _
    calc
      _ = Polynomial.finitePowerCombination N e (a : ℚ) *
          Polynomial.finitePowerCombination N e (b : ℚ) := by
        conv_rhs => rw [Polynomial.finitePowerCombination, Finset.sum_mul]
        simp only [smul_mul_assoc]
      _ = Polynomial.finitePowerCombination N e ((a * b : ℕ) : ℚ) := h a b
      _ = Polynomial.finitePowerCombination N (fun i => (b : ℚ) ^ i.val • e i) (a : ℚ) := by
        simp only [Polynomial.finitePowerCombination, Nat.cast_mul, mul_pow, smul_smul]
  intro i
  have hcoeff : (fun j => e i * e j) = fun j => if i = j then e i else 0 := by
    apply Polynomial.finitePowerCombination_coefficients_eq
    intro b
    change (∑ j : Fin N, (b : ℚ) ^ j.val • (e i * e j)) = _
    calc
      _ = e i * Polynomial.finitePowerCombination N e (b : ℚ) := by
        conv_rhs => rw [Polynomial.finitePowerCombination, Finset.mul_sum]
        simp only [mul_smul_comm]
      _ = (b : ℚ) ^ i.val • e i := congrFun (heigen b) i
      _ = Polynomial.finitePowerCombination N (fun j => if i = j then e i else 0) (b : ℚ) := by
        simp [Polynomial.finitePowerCombination]
  intro j
  exact congrFun hcoeff j

end Algebra
