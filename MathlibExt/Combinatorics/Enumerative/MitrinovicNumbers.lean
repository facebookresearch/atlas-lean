/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Ring

/-! # Mitrinović's numbers

The coefficients of the product of the factors `X - (a + b * i)` satisfy the defining
recurrence of Mitrinović's numbers. Translating the product for `a = 0` gives the binomial
expansion in the first parameter. At `a = 0`, each coefficient is a power of `-b` times an
unsigned Stirling number of the first kind.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Mitrinović's numbers.** For complex numbers $a$ and $b$, Mitrinović's numbers
$R^k_j(a, b)$, $j, k \in \mathbb{N}$ (lower index $j$, upper index $k$), are defined by
$R^k_0(a, b) = 1$ if $k = 0$ and $R^k_0(a, b) = 0$ otherwise, and, for all $j, k$, by
$R^0_{j+1}(a, b) = -(a + b j)\, R^0_j(a, b)$ and
$R^{k+1}_{j+1}(a, b) = R^k_j(a, b) - (a + b j)\, R^{k+1}_j(a, b)$.

With $R = 0$ at negative indices this is the recurrence (4.2),
$R^k_j(a, b) = R^{k-1}_{j-1}(a, b) - (a - b + b j)\, R^k_{j-1}(a, b)$ for $j \ge 1$. The start
value is the source's Corollary 5 at $a = 0$ and its solution (4.3) at $j = 0$ for every $a$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public def mitrinovicR (a b : ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, 0 => -(a + b * j) * mitrinovicR a b j 0
  | j + 1, k + 1 => mitrinovicR a b j k - (a + b * j) * mitrinovicR a b j (k + 1)

/-- **Mitrinović's numbers with lower index one.** For all complex numbers $a, b$, Mitrinović's
numbers satisfy $R^0_1(a, b) = -a$ and $R^1_1(a, b) = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public theorem mitrinovicR_one (a b : ℂ) :
    mitrinovicR a b 1 0 = -a ∧ mitrinovicR a b 1 1 = 1 := by
  simp [mitrinovicR]

/-- **Mitrinović's numbers at $a = 0$.** For every complex number $b$, Mitrinović's numbers
$R^k_j(0, b)$ satisfy the following. First, for every $k \in \mathbb{N}$, $R^k_0(0, b) = 1$ if
$k = 0$ and $R^k_0(0, b) = 0$ otherwise. Second, for all $j, k \in \mathbb{N}$,
$R^{k+1}_{j+1}(0, b) = R^k_j(0, b) + (b - b(j + 1))\, R^{k+1}_j(0, b)$. Third, for all
$j, k \in \mathbb{N}$, $R^k_j(0, b) = (-b)^{j-k} c(j, k)$, where $c(j, k)$ is the unsigned
Stirling number of the first kind, which is $0$ for $k > j$, and the exponent $j - k$ is read as
$0$ when $k > j$.

The source prints the last factor of the recurrence as $R^k_{j-1}(a, b)$; it is
$R^k_{j-1}(0, b)$, the case $a = 0$ of (4.2). The source's hypothesis $b \ne 0$ is dropped: at
$b = 0$ both sides of the closed form are $\delta_{j,k}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 5 (`integers-2026-A36-cor-5`). -/
public theorem mitrinovicR_zero_eq (b : ℂ) :
    (∀ k : ℕ, mitrinovicR 0 b 0 k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, mitrinovicR 0 b (j + 1) (k + 1) =
      mitrinovicR 0 b j k + (b - b * (j + 1)) * mitrinovicR 0 b j (k + 1)) ∧
    ∀ j k : ℕ, mitrinovicR 0 b j k = (-b) ^ (j - k) * Nat.stirlingFirst j k := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro j k
    rw [mitrinovicR]
    ring
  · intro j k
    induction j generalizing k with
    | zero => cases k <;> simp [mitrinovicR]
    | succ j ih =>
      cases k with
      | zero =>
        rw [mitrinovicR, ih]
        cases j <;> simp
      | succ k =>
        rw [mitrinovicR, ih, ih, Nat.stirlingFirst_succ_succ]
        simp only [zero_add, Nat.succ_sub_succ_eq_sub, Nat.cast_add, Nat.cast_mul]
        by_cases h : k < j
        · rw [show j - k = j - (k + 1) + 1 by omega, pow_succ]
          ring
        · simp [Nat.stirlingFirst_eq_zero_of_lt (by omega : j < k + 1)]

open Polynomial

private noncomputable def rowPolynomial (b : ℂ) (j : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range j, (X - C (b * i))

private theorem coeff_taylor_rowPolynomial (a b : ℂ) (j k : ℕ) :
    (taylor (-a) (rowPolynomial b j)).coeff k = mitrinovicR a b j k := by
  induction j generalizing k with
  | zero => simp [rowPolynomial, mitrinovicR, coeff_one]
  | succ j ih =>
    have hfactor : taylor (-a) (X - C (b * j)) = X - C (a + b * j) := by
      rw [map_sub, taylor_X, taylor_C, map_add, map_neg]
      abel
    rw [show rowPolynomial b (j + 1) = rowPolynomial b j * (X - C (b * j)) from
      Finset.prod_range_succ .., taylor_mul, hfactor]
    cases k with
    | zero => simp [ih, mitrinovicR, mul_comm]
    | succ k => rw [coeff_mul_X_sub_C, ih, ih, mul_comm, mitrinovicR]

/-- **Binomial expansion of Mitrinović's numbers in the first parameter.** For all complex
numbers $a, b$ and all $j, k \in \mathbb{N}$, Mitrinović's numbers satisfy
$$R^k_j(a, b) = \sum_{\ell=0}^{j-k} (-1)^\ell \binom{k+\ell}{\ell} a^\ell R^{k+\ell}_j(0, b),$$
where the upper limit $j - k$ is read as $0$ when $k > j$ (both sides are then $0$).

The source's hypothesis $b \ne 0$ is not needed: the identity also holds at $b = 0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 4, Equation (4.6) (`integers-2026-A36-prop-4`). -/
public theorem mitrinovicR_eq_sum_mitrinovicR_zero (a b : ℂ) (j k : ℕ) :
    mitrinovicR a b j k =
      ∑ ℓ ∈ Finset.range (j - k + 1), (-1) ^ ℓ * ((k + ℓ).choose ℓ : ℂ) * a ^ ℓ *
        mitrinovicR 0 b j (k + ℓ) := by
  have hdeg : (rowPolynomial b j).natDegree ≤ j := by
    unfold rowPolynomial
    refine (natDegree_prod_le ..).trans ?_
    simp_rw [natDegree_X_sub_C]
    simp
  have hbound := (natDegree_hasseDeriv_le (rowPolynomial b j) k).trans (Nat.sub_le_sub_right hdeg k)
  rw [← coeff_taylor_rowPolynomial, taylor_coeff, eval_eq_sum_range' (Nat.lt_succ_of_le hbound)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [hasseDeriv_coeff, add_comm ℓ k, Nat.choose_symm_add]
  rw [← coeff_taylor_rowPolynomial 0, neg_zero, taylor_zero, neg_pow]
  ac_rfl

end

end MetaMathlibExt
