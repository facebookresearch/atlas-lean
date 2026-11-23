/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-!
# Alzer–Richards derivative identities

The binomial theorem expands $f^j((1-f)^{n+1}-1)$ and $((1+f)^{n+1}-1)/f^j$ in powers of $f$.
Differentiating these expansions term by term and applying Leibniz's rule gives the identities.
-/

public section

namespace MetaMathlibExt

open Finset

/-- **Alzer–Richards derivative identity for powers of $1 - f$.** Let $r, j, n \ge 0$ be
integers and let $f \colon \mathbb{R} \to \mathbb{R}$ be $r$ times continuously differentiable.
Writing $g^{(i)}$ for the $i$-th derivative of a function $g$ and taking powers of $f$ pointwise,
for every real $x$
$$
\sum_{k=0}^{n} (-1)^{k+1} \binom{n+1}{k+1} \bigl(f^{k+1+j}\bigr)^{(r)}(x) =
\sum_{k=0}^{r} \binom{r}{k} \bigl(f^j\bigr)^{(k)}(x) \,
\bigl((1-f)^{n+1} - 1\bigr)^{(r-k)}(x).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (2). -/
theorem sum_iteratedDeriv_pow_one_sub {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ (k + 1 + j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 - f y) ^ (n + 1) - 1) x := by
  have hfun : (fun y => f y ^ j * ((1 - f y) ^ (n + 1) - 1)) =
      fun y => ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) *
        f y ^ (k + 1 + j) := by
    funext y
    rw [sub_eq_add_neg 1, add_comm 1, add_pow, sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right, mul_sum]
    apply sum_congr rfl
    intro k _
    rw [neg_pow, pow_add (f y) (k + 1) j]
    ac_rfl
  have hsub : ContDiffAt ℝ r (fun y => (1 - f y) ^ (n + 1) - 1) x :=
    ((contDiffAt_const.sub hf.contDiffAt).pow _).sub contDiffAt_const
  rw [← iteratedDeriv_fun_mul (hf.contDiffAt.pow j) hsub, hfun,
    iteratedDeriv_fun_sum (fun k _ => contDiffAt_const.mul (hf.contDiffAt.pow (k + 1 + j)))]
  simp only [iteratedDeriv_const_mul_field]

/-- **Alzer–Richards derivative identity for powers of $1 + f$.** Let $r, j, n \ge 0$ be
integers and let $f \colon \mathbb{R} \to \mathbb{R}$ be $r$ times continuously differentiable
with $f(y) \ne 0$ for every real $y$. Writing $g^{(i)}$ for the $i$-th derivative of a function
$g$ and taking integer powers of $f$ pointwise, for every real $x$
$$
\sum_{k=0}^{n} \binom{n+1}{k+1} \bigl(f^{k+1-j}\bigr)^{(r)}(x) =
\sum_{k=0}^{r} \binom{r}{k} \bigl(1/f^j\bigr)^{(k)}(x) \,
\bigl((1+f)^{n+1} - 1\bigr)^{(r-k)}(x).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (3). -/
theorem sum_iteratedDeriv_zpow_one_add {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (hf0 : ∀ y, f y ≠ 0) (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ ((k : ℤ) + 1 - j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => 1 / f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 + f y) ^ (n + 1) - 1) x := by
  have hpow (k : ℕ) (y : ℝ) :
      f y ^ ((k : ℤ) + 1 - j) = f y ^ (k + 1) / f y ^ j := by
    rw [← Int.natCast_succ, zpow_sub₀ (hf0 y), zpow_natCast, zpow_natCast]
  have expand (y : ℝ) : (1 + f y) ^ (n + 1) - 1 =
      ∑ k ∈ range (n + 1), f y ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) := by
    rw [add_comm 1, add_pow, sum_range_succ']
    simp
  have hfun : (fun y => 1 / f y ^ j * ((1 + f y) ^ (n + 1) - 1)) =
      fun y => ∑ k ∈ range (n + 1),
        ((n + 1).choose (k + 1) : ℝ) * (f y ^ (k + 1) / f y ^ j) := by
    funext y
    rw [expand, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have hden : ContDiffAt ℝ r (fun y => 1 / f y ^ j) x :=
    contDiffAt_const.div (hf.contDiffAt.pow _) (pow_ne_zero _ (hf0 x))
  have hnum : ContDiffAt ℝ r (fun y => (1 + f y) ^ (n + 1) - 1) x :=
    ((contDiffAt_const.add hf.contDiffAt).pow _).sub contDiffAt_const
  have hterm (k : ℕ) : ContDiffAt ℝ r
      (fun y => ((n + 1).choose (k + 1) : ℝ) * (f y ^ (k + 1) / f y ^ j)) x :=
    contDiffAt_const.mul ((hf.contDiffAt.pow _).div (hf.contDiffAt.pow _) (pow_ne_zero _ (hf0 x)))
  simp_rw [hpow]
  rw [← iteratedDeriv_fun_mul hden hnum, hfun, iteratedDeriv_fun_sum (fun k _ => hterm k)]
  simp only [iteratedDeriv_const_mul_field]

end MetaMathlibExt
