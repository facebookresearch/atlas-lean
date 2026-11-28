/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient separation for rational power families

The scalar polynomial `P_a(X)=∑ i : Fin N, a_i X^i` is determined by its evaluations at all
natural numbers. Applying linear forms gives the same coefficient-separation result for
vector-valued families `∑ x^i • v_i` over `ℚ`.

In any `ℚ`-algebra `R`, possibly noncommutative, a family `F(x)=∑ x^i e_i` with
`F(a)F(b)=F(ab)` for all natural `a,b` has pairwise orthogonal idempotent coefficients: `e_i
e_j=e_i` for `i=j` and zero otherwise.

Reference: Bourbaki, *Algebra*, Chapters II and IV.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

universe u v

namespace Polynomial

/-- For `N : ℕ`, `a : Fin N → ℚ`, and `i : Fin N`, `(ofFn N a).coeff i.val = a
i`. -/
theorem finitePowerPolynomial_coeff (N : ℕ) (a : Fin N → ℚ) (i : Fin N) :
    (ofFn N a).coeff i.val = a i := by
  exact ofFn_coeff_eq_val_of_lt a i.isLt

/-- For `N : ℕ`, `a : Fin N → ℚ`, and `x : ℚ`, `(ofFn N a).eval x = ∑ i : Fin N,
a i * x^i.val`. -/
theorem finitePowerPolynomial_eval (N : ℕ) (a : Fin N → ℚ) (x : ℚ) :
    (ofFn N a).eval x = ∑ i : Fin N, a i * x ^ i.val := by
  rw [ofFn_eq_sum_monomial]
  simp only [eval_finsetSum, eval_monomial]

/-- For `N : ℕ` and `a,b : Fin N → ℚ`, if `∑ i, a i * m^i.val = ∑ i, b i * m^i.val` in `ℚ` for
every `m : ℕ`, then `a=b`. -/
theorem finitePowerPolynomial_coefficients_eq (N : ℕ) (a b : Fin N → ℚ)
    (h : ∀ m : ℕ, (∑ i : Fin N, a i * (m : ℚ) ^ i.val) =
      ∑ i : Fin N, b i * (m : ℚ) ^ i.val) : a = b := by
  have hp : ofFn N a = ofFn N b := by
    apply eq_of_infinite_eval_eq
    have hi : Set.Infinite (Set.range (fun m : ℕ => (m : ℚ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply hi.mono
    rintro x ⟨m, rfl⟩
    change (ofFn N a).eval (m : ℚ) = (ofFn N b).eval (m : ℚ)
    simpa only [finitePowerPolynomial_eval] using h m
  funext i
  simpa only [finitePowerPolynomial_coeff] using congrArg (fun p => p.coeff i.val) hp

section Weighted

variable {I : Type v} [Fintype I] {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- For a finite type `I`, a `ℚ`-vector space `V`, exponents `e : I → ℕ`, vectors `v : I → V`, and
`a : ℚ`, `finiteWeightedPowerCombination e v a = ∑ i : I, a^(e i) • v i`. Repeated exponents
are allowed. -/
def finiteWeightedPowerCombination (e : I → ℕ) (v : I → V) (a : ℚ) : V :=
  ∑ i : I, a ^ e i • v i

end Weighted

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- For a `ℚ`-vector space `V`, `N : ℕ`, vectors `a : Fin N → V`, and `x : ℚ`,
`finitePowerCombination N a x = ∑ i : Fin N, x^i.val • a i`. -/
def finitePowerCombination (N : ℕ) (a : Fin N → V) (x : ℚ) : V :=
  finiteWeightedPowerCombination (fun i : Fin N => i.val) a x

/-- For a `ℚ`-vector space `V`, `N : ℕ`, and `a,b : Fin N → V`, if `finitePowerCombination N a m =
finitePowerCombination N b m` for every natural `m` coerced to `ℚ`, then `a=b`. -/
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
    simpa only [finitePowerCombination, finiteWeightedPowerCombination, map_sum, map_smul,
        smul_eq_mul, mul_comm] using hm
  rw [map_sub, congrFun hc i, sub_self]

end Polynomial

namespace Algebra

variable {R : Type u} [Ring R] [Algebra ℚ R]

/-- Let `R` be a ring with a `ℚ`-algebra structure and `e : Fin N → R`. Put `F(x)=∑ i : Fin N,
x^i.val • e i`. If `F(a)*F(b)=F(a*b)` for all natural `a,b` coerced to `ℚ`, then for every
`i,j : Fin N`, `e i * e j = if i=j then e i else 0`. -/
theorem finitePowerCombination_coefficients_mul (N : ℕ) (e : Fin N → R)
    (h : ∀ a b : ℕ,
      Polynomial.finitePowerCombination N e (a : ℚ) *
        Polynomial.finitePowerCombination N e (b : ℚ) =
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
        conv_rhs => rw [Polynomial.finitePowerCombination,
            Polynomial.finiteWeightedPowerCombination, Finset.sum_mul]
        simp only [smul_mul_assoc]
      _ = Polynomial.finitePowerCombination N e ((a * b : ℕ) : ℚ) := h a b
      _ = Polynomial.finitePowerCombination N (fun i => (b : ℚ) ^ i.val • e i) (a : ℚ) := by
        simp only [Polynomial.finitePowerCombination, Polynomial.finiteWeightedPowerCombination,
            Nat.cast_mul, mul_pow, smul_smul]
  intro i
  have hcoeff : (fun j => e i * e j) = fun j => if i = j then e i else 0 := by
    apply Polynomial.finitePowerCombination_coefficients_eq
    intro b
    change (∑ j : Fin N, (b : ℚ) ^ j.val • (e i * e j)) = _
    calc
      _ = e i * Polynomial.finitePowerCombination N e (b : ℚ) := by
        conv_rhs => rw [Polynomial.finitePowerCombination,
            Polynomial.finiteWeightedPowerCombination, Finset.mul_sum]
        simp only [mul_smul_comm]
      _ = (b : ℚ) ^ i.val • e i := congrFun (heigen b) i
      _ = Polynomial.finitePowerCombination N (fun j => if i = j then e i else 0) (b : ℚ) := by
        simp [Polynomial.finitePowerCombination, Polynomial.finiteWeightedPowerCombination]
  intro j
  exact congrFun hcoeff j

end Algebra
