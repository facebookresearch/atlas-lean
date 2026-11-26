/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # No near `F_k`-perfect number of the form `p₁ ^ a * p₂`

This module defines `[k,ℓ]`-near-perfect and near `F_k`-perfect numbers and proves that
`p₁ ^ a * p₂` is not near `F_k`-perfect for distinct odd primes `p₁`, `p₂` and `k > 1`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 17.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

/-- **No near $F_k$-perfect number of the form $p_1^a p_2$.** Let $k > 1$, let $p_1$ and $p_2$ be
distinct odd primes and let $a$ be a natural number. Then $p_1^a p_2$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 17. -/
theorem not_isNearFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂) := by
  have _hk0 : k ≠ 0 := by omega
  rintro ⟨d, hd, hlt, hsum⟩
  have hn_odd : Odd (p₁ ^ a * p₂) := Odd.mul ho₁.pow ho₂
  have hd_odd : Odd d := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    have h2d : 2 ∣ d := even_iff_two_dvd.mp hcon
    have h2n : 2 ∣ p₁ ^ a * p₂ := h2d.trans hd
    exact (Odd.not_two_dvd_nat hn_odd) h2n
  have hcop : Nat.Coprime (p₁ ^ a) p₂ :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes hp₁ hp₂).mpr hne)
  have h1mem : (1 : ℕ) ∉ ({p₂} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp₂.ne_one.symm
  have hsig2 : ArithmeticFunction.sigma k p₂ = 1 + p₂ ^ k := by
    simp only [ArithmeticFunction.sigma_apply, hp₂.divisors, Finset.sum_insert h1mem,
      Finset.sum_singleton, one_pow]
  have hsig : (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) =
      (ArithmeticFunction.sigma k (p₁ ^ a)) * (1 + p₂ ^ k) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2]
  have hbase_even : Even (1 + p₂ ^ k) := Odd.add_odd odd_one ho₂.pow
  have hLHS_even : Even (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) := by
    rw [hsig]
    exact Even.mul_left hbase_even _
  have hn_pow_odd : Odd ((p₁ ^ a * p₂) ^ k) := hn_odd.pow
  have hd_pow_odd : Odd (d ^ k) := hd_odd.pow
  have h3n_odd : Odd (3 * (p₁ ^ a * p₂)) :=
    Odd.mul (⟨1, rfl⟩ : Odd (3 : ℕ)) hn_odd
  have hRHS_odd : Odd ((p₁ ^ a * p₂) ^ k + d ^ k + 3 * (p₁ ^ a * p₂)) :=
    Even.add_odd (Odd.add_odd hn_pow_odd hd_pow_odd) h3n_odd
  rw [hsum] at hLHS_even
  exact (Nat.not_even_iff_odd.mpr hRHS_odd) hLHS_even

end MathlibExt.NumberTheory.FkPerfectWanted
