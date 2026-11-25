/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.Ring

/-!
# Gould's reciprocal binomial identity

H. W. Gould gives the identity in *Combinatorial Identities: A Standardized Set of Tables
Listing 500 Binomial Coefficient Summations* (1972), p. 6, as cited by Horst Alzer and Man Kam
Kwong in *Ramanujan and a Combinatorial Identity Involving Harmonic Numbers*,
*Journal of Integer Sequences* 29 (2026), Article 26.4.8, Lemma 7, equation (2.4).

Pascal's identity gives a difference of two sums with one fewer term, at `x` and `x - 1`.
Their falling product denominators differ by the first and last factors of the next product.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

open Finset

private lemma sum_range_choose_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ range (n + 2), f i * ((n + 1).choose i : ℝ)) =
      (∑ i ∈ range (n + 1), f i * (n.choose i : ℝ)) +
        ∑ i ∈ range (n + 1), f (i + 1) * (n.choose i : ℝ) := by
  rw [sum_range_succ' (fun i => f i * ((n + 1).choose i : ℝ)),
    sum_range_succ' (fun i => f i * (n.choose i : ℝ))]
  simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_succ_succ', Nat.cast_add,
    mul_add, sum_add_distrib]
  rw [sum_range_succ (fun i => f (i + 1) * (n.choose (i + 1) : ℝ)),
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, add_zero]
  ac_rfl

/-- The alternating reciprocal binomial sum on `range (n + 1)`. -/
private noncomputable def alternatingChooseSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), ((-1 : ℝ) ^ i / (x - (i : ℝ))) * (n.choose i : ℝ)

private lemma alternatingChooseSum_succ (n : ℕ) (x : ℝ) :
    alternatingChooseSum (n + 1) x = alternatingChooseSum n x - alternatingChooseSum n (x - 1) := by
  unfold alternatingChooseSum
  rw [sum_range_choose_succ, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_succ, pow_succ, mul_neg_one, neg_div, neg_mul, sub_sub, add_comm (1 : ℝ)]

/-- The product of the first `n` descending factors at `x`. -/
private noncomputable def fallingProduct (n : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ range n, (x - (i : ℝ))

private lemma fallingProduct_succ (n : ℕ) (x : ℝ) :
    fallingProduct (n + 1) x = fallingProduct n x * (x - (n : ℝ)) := by
  exact prod_range_succ _ _

private lemma fallingProduct_succ_shift (n : ℕ) (x : ℝ) :
    fallingProduct (n + 1) x = fallingProduct n (x - 1) * x := by
  unfold fallingProduct
  rw [prod_range_succ', Nat.cast_zero, sub_zero]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [Nat.cast_succ, sub_sub, add_comm (1 : ℝ)]

private lemma fallingProduct_ne_zero {n : ℕ} {x : ℝ} (hx : ∀ i < n, x ≠ (i : ℝ)) :
    fallingProduct n x ≠ 0 := by
  exact prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hx i (mem_range.mp hi))

private lemma alternatingChooseSum_eq (n : ℕ) (x : ℝ) (hx : ∀ i < n + 1, x ≠ (i : ℝ)) :
    alternatingChooseSum n x = (-1 : ℝ) ^ n * (n.factorial : ℝ) / fallingProduct (n + 1) x := by
  induction n generalizing x with
  | zero => simp [alternatingChooseSum, fallingProduct]
  | succ n ih =>
    have hx₀ : ∀ i < n + 1, x ≠ (i : ℝ) := fun i hi => hx i (Nat.lt_succ_of_lt hi)
    have hx₁ : ∀ i < n + 1, x - 1 ≠ (i : ℝ) := by
      intro i hi h
      apply hx (i + 1) (Nat.succ_lt_succ hi)
      rw [Nat.cast_succ, ← h, sub_add_cancel]
    rw [alternatingChooseSum_succ, ih x hx₀, ih (x - 1) hx₁]
    apply (eq_div_iff (fallingProduct_ne_zero hx)).mpr
    rw [sub_mul]
    -- Cancel the shorter products using the two factorizations of the longer one.
    conv_lhs =>
      congr
      · rw [fallingProduct_succ (n + 1) x, ← mul_assoc,
          div_mul_cancel₀ _ (fallingProduct_ne_zero hx₀)]
      · rw [fallingProduct_succ_shift (n + 1) x, ← mul_assoc,
          div_mul_cancel₀ _ (fallingProduct_ne_zero hx₁)]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
    ring

private lemma fallingProduct_eq_factorial_mul_choose (n : ℕ) (x : ℝ) :
    fallingProduct n x = (n.factorial : ℝ) * Ring.choose x n := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.aeval_eq_smeval,
    Polynomial.aeval_def, ← Polynomial.eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range]
  rfl

/-- **Gould's reciprocal binomial identity (Alzer–Kwong, Lemma 7).** Let $N$ be a natural number
and $x$ a real number with $x \ne \nu$ for every $\nu \in \{0, 1, \dots, N\}$. Then
$$
\sum_{\nu=0}^{N} \frac{(-1)^\nu}{x - \nu} \binom{N}{\nu} = \frac{(-1)^N}{(x - N) \binom{x}{N}},
$$
where $\binom{x}{N} = x(x-1)\cdots(x-N+1)/N!$ is the generalized binomial coefficient.

Source: H. W. Gould, *Combinatorial Identities: A Standardized Set of Tables Listing 500 Binomial
Coefficient Summations* (1972), p. 6, as cited by Horst Alzer and Man Kam Kwong, *Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers*, Lemma 7, equation (2.4). -/
public theorem sum_neg_one_pow_div_mul_choose_eq
    (N : ℕ) (x : ℝ)
    (hx : ∀ ν ∈ Finset.Icc 0 N, x ≠ (ν : ℝ)) :
    ∑ ν ∈ Finset.Icc 0 N,
        ((-1 : ℝ) ^ ν / (x - (ν : ℝ))) *
          (Nat.choose N ν : ℝ) =
      (-1 : ℝ) ^ N / ((x - (N : ℝ)) * Ring.choose x N) := by
  rw [← Nat.range_succ_eq_Icc_zero] at hx ⊢
  change alternatingChooseSum N x = _
  rw [alternatingChooseSum_eq N x (fun i hi => hx i (mem_range.mpr hi)), fallingProduct_succ,
    fallingProduct_eq_factorial_mul_choose, mul_assoc,
    mul_comm (Ring.choose x N) (x - (N : ℝ)), mul_comm (N.factorial : ℝ)]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
