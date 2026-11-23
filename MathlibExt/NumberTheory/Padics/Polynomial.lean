/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace Polynomial

/-!
# The p-adic valuation of an integer polynomial

For a nonzero polynomial over the integers, this file defines its `p`-adic valuation as the
minimum of the `p`-adic valuations of its nonzero coefficients.

The definition follows Itamar Nir, arXiv:2608.00668v1, line 419.
-/

/-- **The $p$-adic valuation of an integer polynomial.** Let $p$ be a prime and let
$f \in \mathbb{Z}[X]$ be a nonzero polynomial, with $a_n$ the coefficient of $X^n$ in $f$. Writing
$v_p(a)$ for the $p$-adic valuation of an integer $a$, the $p$-adic valuation of $f$ is the
natural number $v_p(f) = \min \{ v_p(a_n) : a_n \neq 0 \}$. -/
@[nolint unusedArguments]
def padicValuation (p : ℕ) (_hp : Nat.Prime p) (f : Polynomial ℤ) (hf : f ≠ 0) : ℕ :=
  (f.support.image (fun n => padicValInt p (f.coeff n))).min'
    ((support_nonempty.mpr hf).image fun n => padicValInt p (f.coeff n))

/-- **The valuation of a polynomial is at most that of each nonzero coefficient.** Let $p$ be a
prime, write $v_p(a)$ for the $p$-adic valuation of an integer $a$, let $f \in \mathbb{Z}[X]$ be a
nonzero polynomial with $a_n$ the coefficient of $X^n$ in $f$, and let
$v_p(f) = \min \{ v_p(a_n) : a_n \neq 0 \}$ be its $p$-adic valuation. If $a_n \neq 0$, then
$v_p(f) \le v_p(a_n)$. -/
theorem padicValuation_le_coeff {p : ℕ} {hp : Nat.Prime p} {f : Polynomial ℤ} {hf : f ≠ 0}
    {n : ℕ} (hn : n ∈ f.support) :
    padicValuation p hp f hf ≤ padicValInt p (f.coeff n) := by
  unfold padicValuation
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem (fun n => padicValInt p (f.coeff n)) hn)

/-- **Lower bounds for the valuation of a polynomial.** Let $p$ be a prime, write $v_p(a)$ for
the $p$-adic valuation of an integer $a$, let $f \in \mathbb{Z}[X]$ be a nonzero polynomial with
$a_n$ the coefficient of $X^n$ in $f$, and let $v_p(f) = \min \{ v_p(a_n) : a_n \neq 0 \}$ be its
$p$-adic valuation. If $k$ is a natural number with $k \le v_p(a_n)$ for every $n$ with
$a_n \neq 0$, then $k \le v_p(f)$. -/
theorem le_padicValuation {p : ℕ} {hp : Nat.Prime p} {f : Polynomial ℤ} {hf : f ≠ 0}
    {k : ℕ} (hk : ∀ n ∈ f.support, k ≤ padicValInt p (f.coeff n)) :
    k ≤ padicValuation p hp f hf := by
  unfold padicValuation
  apply Finset.le_min'
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact hk n hn

/-- **The valuation of a nonzero constant polynomial.** Let $p$ be a prime and let $a$ be a
nonzero integer. The $p$-adic valuation of the constant polynomial $a \in \mathbb{Z}[X]$, the
minimum of the $p$-adic valuations of its nonzero coefficients, equals the $p$-adic valuation
$v_p(a)$ of the integer $a$. -/
@[simp]
theorem padicValuation_C (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (ha : a ≠ 0) :
    padicValuation p hp (C a) (C_ne_zero.mpr ha) = padicValInt p a := by
  apply le_antisymm
  · have h0 : 0 ∈ (C a : Polynomial ℤ).support := by
      rw [support_C ha]
      exact Finset.mem_singleton_self 0
    calc
      padicValuation p hp (C a) (C_ne_zero.mpr ha) ≤ padicValInt p ((C a).coeff 0) :=
        padicValuation_le_coeff h0
      _ = padicValInt p a := by rw [coeff_C_zero]
  · apply le_padicValuation
    intro n hn
    rw [support_C ha] at hn
    rw [Finset.mem_singleton.mp hn, coeff_C_zero]

end Polynomial
