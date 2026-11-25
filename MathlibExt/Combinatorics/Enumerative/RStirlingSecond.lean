/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedStirlingNumbers

/-!
# r-Stirling numbers of the second kind

`rStirlingSecond n m r` is Broder's `{n \brace m}_r`, the number of partitions of
`{1, …, n}` into `m` blocks with `1, …, r` in distinct blocks, in the indexing of
`rStirlingFirst n m r`. It is given by the finite sum
`{n+r \brace m+r}_r = ∑_i C(n,i) {n-i \brace m} r^i`, the coefficient form of the exponential
generating function `∑_n {n+r \brace m+r}_r z^n/n! = e^{rz} (e^z - 1)^m / m!`, and agrees
with `generalizedStirlingSecond n m r`.
-/

@[expose] public section

namespace MetaMathlibExt

open Finset

/-- **r-Stirling numbers of the second kind.** For natural numbers $n$, $m$ and $r$, Broder's
r-Stirling number of the second kind ${n \brace m}_r$ is $0$ unless $r \le m$ and $r \le n$, and
otherwise
$${n \brace m}_r = \sum_{i=0}^{n-r} \binom{n-r}{i} {n-r-i \brace m-r} r^i,$$
where ${a \brace b}$ denotes the Stirling number of the second kind (and $0^0 = 1$).

Source: A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259;
Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central
Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Section 4
(exponential generating function of `{m+v \brace k+v}_v`). -/
def rStirlingSecond (n m r : ℕ) : ℕ :=
  if r ≤ m ∧ r ≤ n then
    ∑ i ∈ range (n - r + 1), (n - r).choose i * Nat.stirlingSecond (n - r - i) (m - r) * r ^ i
  else 0

/-- **Finite-sum formula for r-Stirling numbers of the second kind.** For all natural numbers
$n$, $m$ and $r$, the r-Stirling number of the second kind ${n+r \brace m+r}_r$ satisfies
$${n+r \brace m+r}_r = \sum_{i=0}^{n} \binom{n}{i} {n-i \brace m} r^i,$$
where ${a \brace b}$ denotes the Stirling number of the second kind (and $0^0 = 1$).

Source: A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259. -/
theorem rStirlingSecond_add_add (n m r : ℕ) :
    rStirlingSecond (n + r) (m + r) r =
      ∑ i ∈ range (n + 1), n.choose i * Nat.stirlingSecond (n - i) m * r ^ i := by
  simp [rStirlingSecond]

/-- **Vanishing of r-Stirling numbers of the second kind.** For natural numbers $n$, $m$ and
$r$ with $m < r$ or $n < r$, the r-Stirling number of the second kind ${n \brace m}_r$ is $0$.

Source: A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259. -/
theorem rStirlingSecond_eq_zero {n m r : ℕ} (h : m < r ∨ n < r) : rStirlingSecond n m r = 0 := by
  simp only [rStirlingSecond, ite_eq_right_iff]
  intro h'
  omega

/-- **r-Stirling numbers of the second kind for r = 0.** For all natural numbers $n$ and $m$,
the r-Stirling number of the second kind ${n \brace m}_0$ equals the Stirling number of the
second kind ${n \brace m}$.

Source: A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259. -/
theorem rStirlingSecond_zero_right (n m : ℕ) : rStirlingSecond n m 0 = Nat.stirlingSecond n m := by
  have h := rStirlingSecond_add_add n m 0
  simp only [add_zero] at h
  rw [h, sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- **r-Stirling numbers of the second kind with exactly r blocks.** For all natural numbers $n$
and $r$, the r-Stirling number of the second kind ${n+r \brace r}_r$ equals $r^n$ (with
$0^0 = 1$).

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Section 4 (exponential generating function at `k = 0`). -/
theorem rStirlingSecond_add_self (n r : ℕ) : rStirlingSecond (n + r) r r = r ^ n := by
  have h := rStirlingSecond_add_add n 0 r
  simp only [zero_add] at h
  rw [h, sum_eq_single n]
  · simp
  · intro i hi hin
    obtain ⟨j, hj⟩ : ∃ j, n - i = j + 1 := ⟨n - i - 1, by have := mem_range.mp hi; omega⟩
    rw [hj, Nat.stirlingSecond_succ_zero]
    simp
  · simp

/-- **r-Stirling numbers as generalized Stirling numbers.** For all natural numbers $n$, $m$
and $r$, the r-Stirling number of the second kind ${n+r \brace m+r}_r$, viewed as a real number,
equals the generalized Stirling number of the second kind of $n$ and $m$ (after Carlitz and
Broder) at the real parameter $x = r$.

Source: A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259. -/
theorem rStirlingSecond_add_add_eq_generalizedStirlingSecond (n m r : ℕ) :
    (rStirlingSecond (n + r) (m + r) r : ℝ) = generalizedStirlingSecond n m r := by
  rw [rStirlingSecond_add_add, generalizedStirlingSecond]
  push_cast
  symm
  apply sum_subset
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i hi hi'
    simp only [mem_range, not_lt] at hi hi'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega)]
    simp

end MetaMathlibExt
