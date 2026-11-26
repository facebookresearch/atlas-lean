/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NegRFibonacciPolynomial

/-!
# Binomial sum for the negative-order Fibonacci polynomials

We express each negative-order Fibonacci polynomial as a finite binomial sum indexed
by the exponent of the inverse unit.
-/

namespace MetaMathlibExt

/-- **Explicit sum for the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. For every
$n \ge 0$,
$$U_{n+1} = \sum_{k=0}^{\lfloor n/r \rfloor} \binom{k}{n - rk} y^{-k} (-x)^{n-rk},$$
where $\binom{a}{b} = 0$ for $b > a$, so the terms with $(r+1) k < n$ vanish.

The paper states $n \ge 1$ and $x$ a unit; the identity holds for $n = 0$ and every $x$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem negRFibonacci_succ_eq_sum {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ Finset.range (n / r + 1),
          ((k.choose (n - r * k) : ℕ) : A) * (↑y⁻¹ : A) ^ k * (-x) ^ (n - r * k) := by
  rw [negRFibonacci_succ_eq_sum' hr x y n]
  let term (j : ℕ) : A :=
    (((n - j) / r).choose j : A) * (↑y⁻¹ : A) ^ ((n - j) / r) * (-x) ^ j
  -- The extra indices have zero binomial coefficient, so the bijection can use all j ≤ n.
  have hsum :
      ∑ j ∈ (Finset.range (n / r + 1)).filter (fun j => r ∣ n - j), term j =
        ∑ j ∈ (Finset.range (n + 1)).filter (fun j => r ∣ n - j), term j := by
    apply Finset.sum_subset
    · exact Finset.filter_subset_filter _
        (Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self n r)))
    · intro j hj hj'
      have hlarge : n / r < j := by
        by_contra! hjle
        exact hj' (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjle), (Finset.mem_filter.mp hj).2⟩)
      have hchoose : (n - j) / r < j :=
        (Nat.div_le_div_right (Nat.sub_le n j)).trans_lt hlarge
      simp [term, Nat.choose_eq_zero_of_lt hchoose]
  change (∑ j ∈ _, term j) = _
  rw [hsum]
  have hr' : 0 < r := by omega
  have hsub (k : ℕ) (hk : k ∈ Finset.range (n / r + 1)) : n - (n - r * k) = r * k := by
    apply Nat.sub_sub_self
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hr').mp (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  symm
  refine Finset.sum_nbij' (fun k => n - r * k) (fun j => (n - j) / r) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..)), ?_⟩
    rw [hsub k hk]
    exact dvd_mul_right r k
  · intro j _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.sub_le n j)))
  · intro k hk
    rw [hsub k hk, Nat.mul_div_cancel_left _ hr']
  · intro j hj
    obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hj
    rw [Nat.mul_div_cancel' hd, Nat.sub_sub_self (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  · intro k hk
    simp only [term, hsub k hk, Nat.mul_div_cancel_left _ hr']

end MetaMathlibExt
