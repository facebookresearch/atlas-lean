/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Stirling numbers of the first kind.** For natural numbers $n$, $m$ and a real
number $x$, the generalized Stirling number of the first kind is

$${n \brack m}_x = \sum_{i=0}^{n-m} \binom{i+m}{m} {n \brack i+m} x^i,$$

where ${n \brack k}$ is the unsigned Stirling number of the first kind, the number of permutations
of $n$ elements with exactly $k$ cycles. For $m > n$ the sum consists of the single term $i = 0$,
which is ${n \brack m} = 0$, so ${n \brack m}_x = 0$.

Source: Carlitz and Broder, as recorded in Cereceda, arXiv:2401.13696v4, lines 132-142;
Axioms 14 (2025), 746. -/
noncomputable def generalizedStirlingFirst (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i)

/-- **Generalized Stirling numbers of the second kind.** For natural numbers $n$, $m$ and a real
number $x$, the generalized Stirling number of the second kind is

$${n \brace m}_x = \sum_{i=0}^{n-m} \binom{n}{i} {n-i \brace m} x^i,$$

where ${n \brace k}$ is the Stirling number of the second kind, the number of partitions of an
$n$-element set into $k$ nonempty blocks. For $m > n$ the sum consists of the single term $i = 0$,
which is $\binom{n}{0} {n \brace m} = 0$, so ${n \brace m}_x = 0$.

Source: Carlitz and Broder, as recorded in Cereceda, arXiv:2401.13696v4, lines 132-142;
Axioms 14 (2025), 746. -/
noncomputable def generalizedStirlingSecond (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i)

/-- **Sum formula for generalized Stirling numbers of the first kind.** For natural numbers
$m \le n$ and every real number $x$, the generalized Stirling number of the first kind satisfies

$${n \brack m}_x = \sum_{i=0}^{n-m} \binom{i+m}{m} {n \brack i+m} x^i,$$

where ${n \brack k}$ is the unsigned Stirling number of the first kind; the sum includes both
endpoints $i = 0$ and $i = n - m$.

Source: Cereceda, arXiv:2401.13696v4, lines 132-142. -/
theorem generalizedStirlingFirst_eq_sum (n m : ℕ) (x : ℝ) (_h : m ≤ n) :
    generalizedStirlingFirst n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i) := rfl

/-- **Sum formula for generalized Stirling numbers of the second kind.** For natural numbers
$m \le n$ and every real number $x$, the generalized Stirling number of the second kind satisfies

$${n \brace m}_x = \sum_{i=0}^{n-m} \binom{n}{i} {n-i \brace m} x^i,$$

where ${n \brace k}$ is the Stirling number of the second kind; the sum includes both endpoints
$i = 0$ and $i = n - m$.

Source: Cereceda, arXiv:2401.13696v4, lines 132-142. -/
theorem generalizedStirlingSecond_eq_sum (n m : ℕ) (x : ℝ) (_h : m ≤ n) :
    generalizedStirlingSecond n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) := rfl

end

end MetaMathlibExt
