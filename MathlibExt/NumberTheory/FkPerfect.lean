/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Near-perfect and deficient-perfect numbers

These predicates express the near-perfect and deficient-perfect conditions using sums of
powers of divisors. For a near-perfect number of the form `2 * p ^ a`, we reduce the
divisor-sum identity modulo two and modulo powers of the odd prime `p`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-deficient-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$
and $d$, the number $n$ is $[k,\ell]$-deficient-perfect with divisor $d$ when $d$ is a proper
divisor of $n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) + d^k = n^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLDeficientPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) + d ^ k = n ^ k + l * n

/-- **$[k,\ell]$-deficient-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-deficient-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) + d^k = n^k + \ell n$. -/
def IsKLDeficientPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLDeficientPerfectWith k l n d

/-- **$[k,\ell]$-near-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$ and
$d$, the number $n$ is $[k,\ell]$-near-perfect with divisor $d$ when $d$ is a proper divisor of
$n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) = n^k + d^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLNearPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) = n ^ k + d ^ k + l * n

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$. -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

/-- **Deficient $F$-perfect numbers.** For a natural number $n$, write
$\sigma_2(n) = \sum_{e \mid n} e^2$. The number $n$ is deficient $F$-perfect when it is
$[2,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_2(n) + d^2 = n^2 + 3n$. -/
def IsDeficientFPerfect (n : ℕ) : Prop :=
  IsKLDeficientPerfect 2 3 n

/-- **Near $F$-perfect numbers.** A natural number $n$ is near $F$-perfect when it is
$[2,3]$-near-perfect, that is, when some proper divisor $d$ of $n$ ($d \mid n$ and $d < n$)
satisfies $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n) = \sum_{e \mid n} e^2$ is the sum
of the squares of the divisors of $n$. -/
def IsNearFPerfect (n : ℕ) : Prop :=
  IsKLNearPerfect 2 3 n

private theorem divisor_sum_modEq {p a k l d m : ℕ} (hk : k ≠ 0)
    (hm : m ∣ 2 * p ^ a) (hpk : m ∣ p ^ k)
    (h : (1 + 2 ^ k) * (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) =
      (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a)) :
    1 + 2 ^ k ≡ d ^ k [MOD m] := by
  have hsum : (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) ≡ 1 [MOD m] := by
    calc
      _ ≡ p ^ (0 * k) [MOD m] := by
        apply Nat.sum_modEq_single (s := Finset.range (a + 1)) (f := fun i ↦ p ^ (i * k)) (by simp)
        intro i _ hi
        rw [Nat.mul_comm, pow_mul]
        exact (hpk.trans (dvd_pow_self _ hi)).modEq_zero_nat
      _ = 1 := by simp
  calc
    1 + 2 ^ k ≡ (1 + 2 ^ k) * (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) [MOD m] := by
      simpa using hsum.symm.mul_left (1 + 2 ^ k)
    _ = (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a) := h
    _ ≡ d ^ k [MOD m] := by
      simpa using (((hm.pow hk).modEq_zero_nat.add_right (d ^ k)).add
        (hm.mul_left l).modEq_zero_nat)

/-- **A divisibility condition for near-perfect numbers $2p^a$.** Let $p$ be an odd prime, let
$a$, $k$, $\ell$ and $d$ be natural numbers with $k > 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. If $d$ is a proper divisor of $2p^a$ ($d \mid 2p^a$ and
$d < 2p^a$) with $\sigma_k(2p^a) = (2p^a)^k + d^k + \ell \cdot 2p^a$, then $p^2 \mid 1 + 2^k$,
and $a$ is even if and only if $d$ is odd.

This is part 2 of Theorem 14 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem klNearPerfectWith_two_mul_prime_pow_imp
    (p a k l d : ℕ) (hp : p.Prime) (hpo : Odd p) (hk : 1 < k)
    (hl : 1 ≤ l) :
    KLNearPerfectWith k l (2 * p ^ a) d →
      p ^ 2 ∣ 1 + 2 ^ k ∧ (Even a ↔ Odd d) := by
  rintro ⟨hd, hdlt, h⟩
  have hk0 : k ≠ 0 := by omega
  have htwo : ArithmeticFunction.sigma k 2 = 1 + 2 ^ k := by
    simp [ArithmeticFunction.sigma_apply, Nat.Prime.divisors Nat.prime_two]
  rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (hpo.coprime_two_left.pow_right a), htwo, ArithmeticFunction.sigma_apply_prime_pow hp] at h
  have hpar : Even a ↔ Odd d := by
    have hsum : Odd (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) ↔ Even a := by
      simp [Finset.odd_sum_iff_odd_card_odd, hpo.pow, Nat.odd_add_one]
    have hn : Even (2 * p ^ a) := even_two.mul_right _
    have hleft : Odd (1 + 2 ^ k) := (even_two.pow_of_ne_zero hk0).one_add
    have hright : Odd ((2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a)) ↔ Odd d := by
      rw [Nat.odd_add, Nat.odd_add', Nat.odd_pow_iff hk0]
      simp [hn.mul_left l, hn.pow_of_ne_zero hk0]
    simpa only [Nat.odd_mul, hleft, true_and, hsum, hright] using Iff.of_eq (congrArg Odd h)
  refine ⟨?_, hpar⟩
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
    omega
  -- If p does not divide d, then d divides 2, and both possibilities contradict the congruence.
  have hpd : p ∣ d := by
    have hpn : p ∣ 2 * p ^ a := (dvd_pow_self p ha).mul_left 2
    have hmod := divisor_sum_modEq hk0 hpn (dvd_pow_self p hk0) h
    by_contra hnd
    have hd2 := ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right a).dvd_of_dvd_mul_right hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
    · rw [one_pow] at hmod
      exact (hp.coprime_iff_not_dvd.mp hpo.coprime_two_right)
        (hp.dvd_of_dvd_pow (Nat.add_modEq_left_iff.mp hmod))
    · exact hp.not_dvd_one (Nat.add_modEq_right_iff.mp hmod)
  have ha2 : 2 ≤ a := by
    by_contra! ha2
    obtain rfl : a = 1 := by omega
    -- At exponent one, parity and p ∣ d would force d to be the whole number.
    simp only [pow_one] at hd hdlt
    have heven : Even d := by simpa using hpar.not.mp (by decide : ¬ Even 1)
    exact hdlt.ne (Nat.dvd_antisymm hd
      (hpo.coprime_two_left.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp heven) hpd))
  have hmod2 := divisor_sum_modEq hk0 ((pow_dvd_pow p ha2).mul_left 2) (pow_dvd_pow p hk) h
  exact Nat.modEq_zero_iff_dvd.mp (hmod2.trans (pow_dvd_pow_of_dvd_of_le hpd hk).modEq_zero_nat)

end MathlibExt.NumberTheory.FkPerfectWanted
