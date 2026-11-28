/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.Algebra.Polynomial.PrimeValueConditions
public import MathlibExt.NumberTheory.AbsoluteLucasPseudoprimes
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.ThreePrimeDCarmichael
public import MathlibExt.NumberTheory.ThreePrimeDCarmichaelDivisibility
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime k-tuples give infinitely many primary Carmichael numbers

This module shows that the prime k-tuples conjecture yields infinitely many primary
Carmichael numbers with three prime factors. For the linear forms $6x+1$, $12x+1$ and
$18x+1$, the product $(6x+1)(12x+1)(18x+1)$ at every simultaneous prime value is composite,
satisfies $a^{n-1} \equiv 1 \pmod n$ for every $a$ coprime to $n$, and has base-$p$ digit
sum $p$ at each of its three prime factors $p$. The main result is
`infinite_primary_carmichael_of_primeKTuples`.

Sources: Samuel S. Wagstaff, Jr., *Primary Carmichael Numbers*, INTEGERS 22 (2022),
Article A55, Lemma 1, Corollary 1 and Theorem 1; and Ballot's restatement, Christian Ballot,
*On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102, Theorem 2
(`integers-2026-A102-thm-2`).
-/

namespace MetaMathlibExt

/-- For every natural number $y$, if $6y+7$, $12y+13$ and $18y+19$ are all prime, then their
product exceeds $1$, is composite, satisfies $a^{n-1} \equiv 1 \pmod n$ for every natural number
$a$ coprime to it, has exactly three distinct prime factors, and has base-$p$ digit sum $p$ at
each of its prime factors $p$. -/
private theorem chernick_mem {y : ℕ} (hp : (6 * y + 7).Prime) (hq : (12 * y + 13).Prime)
    (hr : (18 * y + 19).Prime) :
    (6 * y + 7) * (12 * y + 13) * (18 * y + 19) ∈
      {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
        n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p} := by
  set N := (6 * y + 7) * (12 * y + 13) * (18 * y + 19) with hNdef
  have hp2 : 2 ≤ 6 * y + 7 := hp.two_le
  have hq2 : 2 ≤ 12 * y + 13 := hq.two_le
  have hr2 : 2 ≤ 18 * y + 19 := hr.two_le
  have hne1 : 6 * y + 7 ≠ 12 * y + 13 := by omega
  have hne2 : 6 * y + 7 ≠ 18 * y + 19 := by omega
  have hne3 : 12 * y + 13 ≠ 18 * y + 19 := by omega
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  have h1N : 1 < N := by
    have e : (2 : ℕ) * 2 * 2 ≤ N := mul_le_mul_three hp2 hq2 hr2
    omega
  have hNp : ¬ N.Prime := by
    have ha1 : (6 * y + 7) * (12 * y + 13) ≠ 1 :=
      ne_of_gt (lt_of_lt_of_le (by decide) (mul_le_mul' hp2 hq2))
    rw [hNdef, Nat.prime_mul_iff]
    rintro (⟨-, hb⟩ | ⟨-, ha⟩)
    · omega
    · exact ha1 ha
  have hN1 : N = (6 * y + 6) * (216 * y ^ 2 + 498 * y + 288) + 1 := by rw [hNdef]; ring
  have hN2 : N = (12 * y + 12) * (108 * y ^ 2 + 249 * y + 144) + 1 := by rw [hNdef]; ring
  have hN3 : N = (18 * y + 18) * (72 * y ^ 2 + 166 * y + 96) + 1 := by rw [hNdef]; ring
  have hs1 : (6 * y + 7) - 1 = 6 * y + 6 := by omega
  have hs2 : (12 * y + 13) - 1 = 12 * y + 12 := by omega
  have hs3 : (18 * y + 19) - 1 = 18 * y + 18 := by omega
  have hd1 : ((6 * y + 7) - 1) ∣ (N - 1) := by
    rw [hs1]; exact ⟨216 * y ^ 2 + 498 * y + 288, by omega⟩
  have hd2 : ((12 * y + 13) - 1) ∣ (N - 1) := by
    rw [hs2]; exact ⟨108 * y ^ 2 + 249 * y + 144, by omega⟩
  have hd3 : ((18 * y + 19) - 1) ∣ (N - 1) := by
    rw [hs3]; exact ⟨72 * y ^ 2 + 166 * y + 96, by omega⟩
  have hcopPQ : (6 * y + 7).Coprime (12 * y + 13) := (Nat.coprime_primes hp hq).mpr hne1
  have hcopPR : (6 * y + 7).Coprime (18 * y + 19) := (Nat.coprime_primes hp hr).mpr hne2
  have hcopQR : (12 * y + 13).Coprime (18 * y + 19) := (Nat.coprime_primes hq hr).mpr hne3
  have hcopPQR : ((6 * y + 7) * (12 * y + 13)).Coprime (18 * y + 19) :=
    Nat.coprime_mul_iff_left.mpr ⟨hcopPR, hcopQR⟩
  have hdvdP : (6 * y + 7) ∣ N := ⟨(12 * y + 13) * (18 * y + 19), by rw [hNdef]; ring⟩
  have hdvdQ : (12 * y + 13) ∣ N := ⟨(6 * y + 7) * (18 * y + 19), by rw [hNdef]; ring⟩
  have hdvdR : (18 * y + 19) ∣ N := ⟨(6 * y + 7) * (12 * y + 13), by rw [hNdef]; ring⟩
  have hpf : N.primeFactors = {(6 * y + 7), (12 * y + 13), (18 * y + 19)} := by
    ext s
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hsdiv, -⟩
      rw [hNdef] at hsdiv
      rcases (hs.dvd_mul.mp hsdiv) with h | h
      · rcases (hs.dvd_mul.mp h) with h1 | h1
        · exact Or.inl (((Nat.Prime.dvd_iff_eq hp hs.ne_one).mp h1).symm)
        · exact Or.inr (Or.inl (((Nat.Prime.dvd_iff_eq hq hs.ne_one).mp h1).symm))
      · exact Or.inr (Or.inr (((Nat.Prime.dvd_iff_eq hr hs.ne_one).mp h).symm))
    · rintro (rfl | rfl | rfl)
      · exact ⟨hp, hdvdP, hN0⟩
      · exact ⟨hq, hdvdQ, hN0⟩
      · exact ⟨hr, hdvdR, hN0⟩
  have hsqf : Squarefree N := by
    rw [hNdef, Nat.squarefree_mul hcopPQR, Nat.squarefree_mul hcopPQ]
    exact ⟨⟨hp.prime.squarefree, hq.prime.squarefree⟩, hr.prime.squarefree⟩
  have h2N : 2 < N := by
    have e : (2 : ℕ) * 2 * 2 ≤ N := mul_le_mul_three hp2 hq2 hr2
    omega
  have hkor : N.IsCarmichael := by
    refine Nat.isCarmichael_iff_korselt.mpr ⟨h2N, hNp, hsqf, fun s hs hsN => ?_⟩
    have hmem : s ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hs, hsN, hN0⟩
    rw [hpf] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hd1
    · exact hd2
    · exact hd3
  have hcarm : ∀ a : ℕ, a.Coprime N → a ^ (N - 1) ≡ 1 [MOD N] := by
    intro a ha
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · rw [Nat.coprime_zero_left] at ha
        omega
      · exact h
    exact (Nat.probablePrime_iff_modEq N ha1).mp (hkor.probablePrime_of_coprime ha)
  have hmem1 : (6 * y + 7) ∉ ({(12 * y + 13), (18 * y + 19)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hmem2 : (12 * y + 13) ∉ ({(18 * y + 19)} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  have hcard : N.primeFactors.card = 3 := by
    rw [hpf, Finset.card_insert_of_notMem hmem1, Finset.card_insert_of_notMem hmem2,
      Finset.card_singleton]
  have hdigP : (Nat.digits (6 * y + 7) N).sum = 6 * y + 7 := by
    have hof : Nat.ofDigits (6 * y + 7) [0, 2, 6 * y, 5] = N := by
      rw [hNdef]; simp only [Nat.ofDigits, Nat.cast_id]; ring
    have hdig : Nat.digits (6 * y + 7) N = [0, 2, 6 * y, 5] := by
      rw [← hof]
      refine Nat.digits_ofDigits _ (by omega) _ ?_ ?_
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> omega
      · simp
    rw [hdig]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hdigQ : (Nat.digits (12 * y + 13) N).sum = 12 * y + 13 := by
    have hof : Nat.ofDigits (12 * y + 13) [0, 3 * y + 3, 9 * y + 10] = N := by
      rw [hNdef]; simp only [Nat.ofDigits, Nat.cast_id]; ring
    have hdig : Nat.digits (12 * y + 13) N = [0, 3 * y + 3, 9 * y + 10] := by
      rw [← hof]
      refine Nat.digits_ofDigits _ (by omega) _ ?_ ?_
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> omega
      · simp
    rw [hdig]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hdigR : (Nat.digits (18 * y + 19) N).sum = 18 * y + 19 := by
    have hof : Nat.ofDigits (18 * y + 19) [0, 14 * y + 15, 4 * y + 4] = N := by
      rw [hNdef]; simp only [Nat.ofDigits, Nat.cast_id]; ring
    have hdig : Nat.digits (18 * y + 19) N = [0, 14 * y + 15, 4 * y + 4] := by
      rw [← hof]
      refine Nat.digits_ofDigits _ (by omega) _ ?_ ?_
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> omega
      · simp
    rw [hdig]
    simp only [List.sum_cons, List.sum_nil]
    omega
  have hdig : ∀ p ∈ N.primeFactors, (Nat.digits p N).sum = p := by
    rw [hpf]
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hdigP
    · exact hdigQ
    · exact hdigR
  exact ⟨h1N, hNp, hcarm, hcard, hdig⟩

/-- **Prime $k$-tuples give infinitely many primary Carmichael numbers (Wagstaff).** Suppose the
prime $k$-tuples conjecture holds in the following form: for every finite list of integer pairs
$(a_1, b_1), \dots, (a_k, b_k)$ with all $a_i \ge 1$ such that for every prime $\ell$ there is an
integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely many natural numbers $x$
for which every $a_i x + b_i$ is a positive prime. Then there are infinitely many composite natural
numbers $n > 1$ such that $a^{n-1} \equiv 1 \pmod n$ for every natural number $a$ coprime to $n$,
$n$ has exactly three distinct prime factors, and for every prime $p \mid n$ the sum of the
base-$p$ digits of $n$ equals $p$.

Sources: Samuel S. Wagstaff, Jr., *Primary Carmichael Numbers*, INTEGERS 22 (2022),
Article A55, Lemma 1, Corollary 1 and Theorem 1; and Ballot's restatement, Christian Ballot,
*On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102, Theorem 2
(`integers-2026-A102-thm-2`). -/
public theorem infinite_primary_carmichael_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p}.Infinite
    := by
  have h1l : ∀ ab ∈ ([(6, 1), (12, 1), (18, 1)] : List (ℤ × ℤ)), 1 ≤ ab.1 := by decide
  have hadm : ∀ ℓ : ℕ, ℓ.Prime →
      ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (([(6, 1), (12, 1), (18, 1)].map fun ab => ab.1 * x + ab.2).prod) := by
    intro ℓ hℓ
    refine ⟨0, ?_⟩
    have hprod : (([(6, 1), (12, 1), (18, 1)].map fun ab => ab.1 * (0 : ℤ) + ab.2).prod) = 1 := by
      decide
    rw [hprod]
    intro hdiv
    have h1 : ℓ ∣ 1 := by exact_mod_cast hdiv
    exact hℓ.ne_one (Nat.dvd_one.mp h1)
  have hS := hk [(6, 1), (12, 1), (18, 1)] h1l hadm
  have hsub1 : {x : ℕ | ∀ ab ∈ [(6, 1), (12, 1), (18, 1)],
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime} ⊆
      {x : ℕ | (6 * x + 1).Prime ∧ (12 * x + 1).Prime ∧ (18 * x + 1).Prime} := by
    intro x hx
    have h6 := hx (6, 1) (by simp)
    have h12 := hx (12, 1) (by simp)
    have h18 := hx (18, 1) (by simp)
    dsimp only at h6 h12 h18
    obtain ⟨-, hp6⟩ := h6
    obtain ⟨-, hp12⟩ := h12
    obtain ⟨-, hp18⟩ := h18
    have c6 : (6 : ℤ) * (x : ℤ) + 1 = ((6 * x + 1 : ℕ) : ℤ) := by push_cast; ring
    have c12 : (12 : ℤ) * (x : ℤ) + 1 = ((12 * x + 1 : ℕ) : ℤ) := by push_cast; ring
    have c18 : (18 : ℤ) * (x : ℤ) + 1 = ((18 * x + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [c6, Int.natAbs_natCast] at hp6
    rw [c12, Int.natAbs_natCast] at hp12
    rw [c18, Int.natAbs_natCast] at hp18
    exact ⟨hp6, hp12, hp18⟩
  have hS' : {x : ℕ | (6 * x + 1).Prime ∧ (12 * x + 1).Prime ∧ (18 * x + 1).Prime}.Infinite :=
    Set.Infinite.mono hsub1 hS
  have hmono : StrictMono (fun x : ℕ => (6 * x + 1) * (12 * x + 1) * (18 * x + 1)) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have g1 : 6 * n + 1 < 6 * (n + 1) + 1 := by omega
    have g2 : 12 * n + 1 < 12 * (n + 1) + 1 := by omega
    have g3 : 18 * n + 1 < 18 * (n + 1) + 1 := by omega
    have s1 : (6 * n + 1) * (12 * n + 1) < (6 * (n + 1) + 1) * (12 * n + 1) :=
      mul_lt_mul_of_pos_right g1 (by omega)
    have s2 : (6 * n + 1) * (12 * n + 1) * (18 * n + 1) <
        (6 * (n + 1) + 1) * (12 * n + 1) * (18 * n + 1) :=
      mul_lt_mul_of_pos_right s1 (by omega)
    have s3 : (6 * (n + 1) + 1) * (12 * n + 1) < (6 * (n + 1) + 1) * (12 * (n + 1) + 1) :=
      mul_lt_mul_of_pos_left g2 (by omega)
    have s4 : (6 * (n + 1) + 1) * (12 * n + 1) * (18 * n + 1) <
        (6 * (n + 1) + 1) * (12 * (n + 1) + 1) * (18 * n + 1) :=
      mul_lt_mul_of_pos_right s3 (by omega)
    have s5 : (6 * (n + 1) + 1) * (12 * (n + 1) + 1) * (18 * n + 1) <
        (6 * (n + 1) + 1) * (12 * (n + 1) + 1) * (18 * (n + 1) + 1) :=
      mul_lt_mul_of_pos_left g3 (mul_pos (by omega) (by omega))
    exact lt_trans s2 (lt_trans s4 s5)
  have hinj : Set.InjOn (fun x : ℕ => (6 * x + 1) * (12 * x + 1) * (18 * x + 1))
      {x : ℕ | (6 * x + 1).Prime ∧ (12 * x + 1).Prime ∧ (18 * x + 1).Prime} :=
    hmono.injective.injOn
  have himg : ((fun x : ℕ => (6 * x + 1) * (12 * x + 1) * (18 * x + 1)) ''
      {x : ℕ | (6 * x + 1).Prime ∧ (12 * x + 1).Prime ∧ (18 * x + 1).Prime}).Infinite := by
    intro hfin
    exact hS' ((Set.finite_image_iff hinj).mp hfin)
  have hsub2 : (fun x : ℕ => (6 * x + 1) * (12 * x + 1) * (18 * x + 1)) ''
        {x : ℕ | (6 * x + 1).Prime ∧ (12 * x + 1).Prime ∧ (18 * x + 1).Prime} ⊆
        {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
          n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p} := by
    rintro n ⟨x, hx, rfl⟩
    dsimp only at ⊢
    simp only [Set.mem_ofPred_eq] at hx
    obtain ⟨hp, hq, hr⟩ := hx
    have hx1 : 1 ≤ x := by have h2 := hp.two_le; omega
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : x ≠ 0)
    have e1 : 6 * (y + 1) + 1 = 6 * y + 7 := by ring
    have e2 : 12 * (y + 1) + 1 = 12 * y + 13 := by ring
    have e3 : 18 * (y + 1) + 1 = 18 * y + 19 := by ring
    rw [e1] at hp
    rw [e2] at hq
    rw [e3] at hr
    rw [e1, e2, e3]
    exact chernick_mem hp hq hr
  exact Set.Infinite.mono hsub2 himg

end MetaMathlibExt
