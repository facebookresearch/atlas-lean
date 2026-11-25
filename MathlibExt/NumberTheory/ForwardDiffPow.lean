/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Iterated forward differences of powers
-/

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

/-- **Iterated forward differences of a power as an alternating binomial sum.** For a real
number $r$, let $\Delta_r$ be the forward difference operator with step $r$, sending a function
$f : \mathbb{R} \to \mathbb{R}$ to $y \mapsto f(y + r) - f(y)$, and let $\Delta_r^k$ be its
$k$-fold iterate (the identity when $k = 0$). For all real numbers $r$ and $x$ and all natural
numbers $k$ and $n$, applying $\Delta_r^k$ to the function $y \mapsto y^n$ and evaluating at $x$
gives $\sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} (x + rj)^n$.

The paper states this for nonzero complex $r$ and positive $k$; here $r$ is real and $k = 0$ is
allowed.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Lemma 21. -/
public theorem iterate_forwardDiff_pow_eq_sum (r x : ℝ)
    (k n : ℕ) :
    ((fun f : ℝ → ℝ => fun y => f (y + r) - f y)^[k]
        (fun y => y ^ n)) x =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) *
        (Nat.choose k j : ℝ) * (x + r * j) ^ n := by
  change (fwdDiff r)^[k] (fun y : ℝ => y ^ n) x = _
  rw [fwdDiff_iter_eq_sum_shift]
  simp [mul_comm r]

open Polynomial in
/-- For any real step, the iterated forward difference of a power vanishes once
the order of the difference exceeds the exponent. -/
public theorem iterate_forwardDiff_pow_eq_zero_of_lt (r : ℝ) {n k : ℕ} (hnk : n < k) :
    (fwdDiff r)^[k] (fun y : ℝ => y ^ n) = 0 := by
  funext x
  let p := (C r * X + C x) ^ n
  have hdeg : p.natDegree ≤ n := by
    simpa [p] using natDegree_pow_le_of_le n (natDegree_linear_le (a := r) (b := x))
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (hdeg.trans_lt hnk)) 0
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  calc
    _ = _ := iterate_forwardDiff_pow_eq_sum r x k n
    _ = _ := by simpa [p, add_comm] using hzero

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
