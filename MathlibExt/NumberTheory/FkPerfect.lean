/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # No product of distinct odd primes is deficient `F_k`-perfect

For `k > 1` and a finite set `s` of odd primes, `∏ p ∈ s, p` is not deficient
`F_k`-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", Theorem 21.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$. -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

private theorem odd_prod_of_odd (s : Finset ℕ) (hs : ∀ p ∈ s, Odd p) :
    Odd (∏ p ∈ s, p) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      simp
  | insert q qs hq ih =>
      intro hs
      rw [Finset.prod_insert hq]
      exact (hs q (Finset.mem_insert_self q qs)).mul
        (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp)))

private theorem sigma_prod_eq (k : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k = ∏ p ∈ s, (1 + p ^ k) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      simp only [Finset.prod_empty, Nat.divisors_one, Finset.sum_singleton, one_pow]
  | insert q qs hq ih =>
      intro hs
      have hs' : ∀ p ∈ qs, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hq' : q.Prime := hs q (Finset.mem_insert_self q qs)
      have hcop : Nat.Coprime q (∏ p ∈ qs, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        exact (Nat.coprime_primes hq' (hs' p hp)).mpr (fun heq => hq (heq ▸ hp))
      have hprime : ∑ e ∈ q.divisors, e ^ k = 1 + q ^ k := by
        have h1 : (1 : ℕ) ∉ ({q} : Finset ℕ) := by
          simpa only [Finset.mem_singleton] using hq'.ne_one.symm
        simp only [hq'.divisors, Finset.sum_insert h1, Finset.sum_singleton, one_pow]
      rw [Finset.prod_insert hq, ← ArithmeticFunction.sigma_apply,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply,
        hprime, ih hs', Finset.prod_insert hq]

/-- **No product of distinct odd primes is deficient $F_k$-perfect.** Let $k > 1$ and let $s$ be a
finite set of odd primes. Then $\prod_{p \in s} p$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 21. -/
theorem not_isDeficientFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsDeficientFkPerfect k (∏ p ∈ s, p) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  have _ : k ≠ 0 := by omega
  have hn : Odd (∏ p ∈ s, p) :=
    odd_prod_of_odd s (fun p hp => (hs p hp).2)
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp only [Finset.prod_empty] at hdvd hlt
    exact (Nat.ne_of_lt hlt) (Nat.dvd_one.mp hdvd)
  · have hσ : Even (∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k) := by
      rw [sigma_prod_eq k s (fun p hp => (hs p hp).1)]
      have hqeven : Even (1 + q ^ k) := ((hs q hq).2.pow).one_add
      rw [← Finset.mul_prod_erase s (fun p => 1 + p ^ k) hq]
      exact hqeven.mul_right _
    have hd : Odd d := by
      rcases Nat.even_or_odd d with hev | hod
      · exfalso
        have h2n : Even (∏ p ∈ s, p) :=
          even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans hdvd)
        have h0 : (∏ p ∈ s, p) % 2 = 0 := Nat.even_iff.mp h2n
        have h1 : (∏ p ∈ s, p) % 2 = 1 := Nat.odd_iff.mp hn
        omega
      · exact hod
    have hσ0 : (∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k) % 2 = 0 := Nat.even_iff.mp hσ
    have hd1 : d ^ k % 2 = 1 := Nat.odd_iff.mp hd.pow
    have hn1 : (∏ p ∈ s, p) ^ k % 2 = 1 := Nat.odd_iff.mp hn.pow
    have h31 : (3 * ∏ p ∈ s, p) % 2 = 1 :=
      Nat.odd_iff.mp ((by decide : Odd 3).mul hn)
    omega

end MathlibExt.NumberTheory.FkPerfectWanted
