/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

/-- **Local factor.** Given $a : \mathbb{N} \to \mathbb{C}$ and natural numbers $p$ and $e$,
the local factor of $a$ at $p$ with exponent $e$ is $1$ if $e = 0$, $a(p)$ if $e = 1$, and $0$
if $e \ge 2$. -/
def chapter5Entry30LocalCoeff (a : ℕ → ℂ) (p e : ℕ) : ℂ :=
  match e with
  | 0 => 1
  | 1 => a p
  | _ + 2 => 0

/-- **Coefficients for Entry 30.** For a function $a : \mathbb{N} \to \mathbb{C}$ and
$n \in \mathbb{N}$, the Entry 30 coefficient $c_a(n) \in \mathbb{C}$ is $0$ when $n = 0$. When
$n \ne 0$ it is the product, over the prime factors $p$ of $n$, of the local factor of $a$ at $p$
with exponent the multiplicity of $p$ in $n$. The local factor at $p$ with exponent $e$ is $1$
for $e = 0$, $a(p)$ for $e = 1$, and $0$ for $e \ge 2$. -/
def chapter5Entry30Coeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else ∏ p ∈ n.primeFactors, chapter5Entry30LocalCoeff a p (n.factorization p)

/-- **Terms of the Dirichlet series over non-squarefree integers.** For $s \in \mathbb{C}$ and a
natural number $j$, put $n = j + 1$; the $j$-th term is $0$ if $n$ is squarefree and $n^{-s}$
otherwise. As $j$ ranges over the natural numbers, these are the terms of $\sum n^{-s}$ over
non-squarefree $n \ge 1$. -/
def chapter5Entry30NonSquarefreeTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n then 0 else (n : ℂ) ^ (-s)

/-- **Terms over squarefree integers with an odd number of prime factors.** For $s \in \mathbb{C}$
and a natural number $j$, put $n = j + 1$; the $j$-th term is $n^{-s}$ if $n$ is squarefree and
has an odd number of distinct prime factors, and $0$ otherwise. As $j$ ranges over the natural
numbers, these are the terms of $\sum n^{-s}$ over squarefree $n \ge 1$ with an odd number of
prime factors. -/
def chapter5Entry30OddTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n ∧ Odd n.primeFactors.card then (n : ℂ) ^ (-s) else 0

/-- **Signed multiplicative coefficient.** For $s \in \mathbb{C}$ and a natural number $n$, let
$a(p) = -p^{-s}$ for natural numbers $p$. The signed coefficient of $n$ is $0$ if $n = 0$ and,
for $n \ne 0$, the product over the prime factors $p$ of $n$ of the local factor of $a$ at $p$
with exponent the multiplicity of $p$ in $n$, where the local factor of $a$ at $p$ with exponent
$e$ is $1$ for $e = 0$, $a(p)$ for $e = 1$, and $0$ for $e \ge 2$. -/
def chapter5Entry30SignedCoeff (s : ℂ) (n : ℕ) : ℂ :=
  chapter5Entry30Coeff (fun p => -((p : ℂ) ^ (-s))) n

/-- **Terms of the Dirichlet series over squarefree integers.** For a complex number $s$ and a
natural number $j$, let $n = j + 1$; the $j$-th squarefree term is $n^{-s}$ if $n$ is squarefree
and $0$ otherwise, so the series of these terms over $j \ge 0$ is $\sum n^{-s}$ over the
squarefree $n \ge 1$. -/
def chapter5Entry30SquarefreeTerm (s : ℂ) (j : ℕ) : ℂ :=
  let n := j + 1
  if Squarefree n then (n : ℂ) ^ (-s) else 0

/-- **Local factor at exponent zero.** For every $a : \mathbb{N} \to \mathbb{C}$ and every natural
number $p$, the local factor of $a$ at $p$ with exponent $0$ is $1$. -/
@[simp]
lemma chapter5Entry30LocalCoeff_zero (a : ℕ → ℂ) (p : ℕ) :
    chapter5Entry30LocalCoeff a p 0 = 1 :=
  rfl

/-- **Local factor at exponent one.** For every $a : \mathbb{N} \to \mathbb{C}$ and every natural
number $p$, the local factor of $a$ at $p$ with exponent $1$ is $a(p)$. -/
@[simp]
lemma chapter5Entry30LocalCoeff_one (a : ℕ → ℂ) (p : ℕ) :
    chapter5Entry30LocalCoeff a p 1 = a p :=
  rfl

/-- **Entry 30 local factors vanish at exponents at least two.** For every function
$a : \mathbb{N} \to \mathbb{C}$, every $p \in \mathbb{N}$ and every $e \ge 2$, the Entry 30 local
factor of $a$ at $p$ with exponent $e$ is $0$. -/
lemma chapter5Entry30LocalCoeff_of_two_le (a : ℕ → ℂ) (p e : ℕ) (he : 2 ≤ e) :
    chapter5Entry30LocalCoeff a p e = 0 := by
  have heq : e = (e - 2) + 2 := by omega
  rw [heq]
  rfl

/-- **Entry 30 coefficients at squarefree integers.** For every function
$a : \mathbb{N} \to \mathbb{C}$ and every squarefree $n \in \mathbb{N}$ with $n \ne 0$, the Entry 30
coefficient $c_a(n)$ is the product of $a(p)$ over the prime factors $p$ of $n$. -/
lemma chapter5Entry30Coeff_of_squarefree (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    chapter5Entry30Coeff a n = ∏ p ∈ n.primeFactors, a p := by
  unfold chapter5Entry30Coeff
  simp only [hn, ↓reduceIte]
  apply Finset.prod_congr rfl
  intro p hp
  have hpos : 0 < n.factorization p := by
    have hmem2 : p ∈ n.factorization.support := by
      rw [Nat.support_factorization]; exact hp
    have hne := Finsupp.mem_support_iff.mp hmem2
    omega
  have hle : n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
  have heq : n.factorization p = 1 := by omega
  change chapter5Entry30LocalCoeff a p (n.factorization p) = a p
  rw [heq]
  rfl

/-- The coefficient vanishes at every non-squarefree `n`. -/
lemma chapter5Entry30Coeff_of_not_squarefree (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hsq : ¬Squarefree n) : chapter5Entry30Coeff a n = 0 := by
  unfold chapter5Entry30Coeff
  simp only [hn, ↓reduceIte]
  have hle : ¬ ∀ p, n.factorization p ≤ 1 :=
    fun h => hsq ((Nat.squarefree_iff_factorization_le_one hn).mpr h)
  push Not at hle
  obtain ⟨p, hp⟩ := hle
  have hge : 2 ≤ n.factorization p := by omega
  have hzero : chapter5Entry30LocalCoeff a p (n.factorization p) = 0 :=
    chapter5Entry30LocalCoeff_of_two_le a p _ hge
  have hmem : p ∈ n.primeFactors := by
    have hne : n.factorization p ≠ 0 := by omega
    have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hne
    rw [Nat.support_factorization] at hmem
    exact hmem
  exact Finset.prod_eq_zero hmem hzero

/-- **Closed form of the Entry 30 coefficients.** For every function $a : \mathbb{N} \to \mathbb{C}$
and every $n \in \mathbb{N}$ with $n \ne 0$, the Entry 30 coefficient $c_a(n)$ equals the product of
$a(p)$ over the prime factors $p$ of $n$ when $n$ is squarefree, and $c_a(n) = 0$ otherwise. -/
lemma chapter5Entry30Coeff_of_ne_zero (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    chapter5Entry30Coeff a n =
      if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0 := by
  split_ifs with hsq
  · exact chapter5Entry30Coeff_of_squarefree a n hn hsq
  · exact chapter5Entry30Coeff_of_not_squarefree a n hn hsq

private lemma e30_rpow_prod (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (z : ℝ) :
    Real.rpow (∏ i ∈ s, f i) z = ∏ i ∈ s, Real.rpow (f i) z := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    have ha : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsub : ∀ i ∈ s, 0 ≤ f i :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hmul : Real.rpow (f a * ∏ i ∈ s, f i) z
        = Real.rpow (f a) z * Real.rpow (∏ i ∈ s, f i) z := by
      simpa using Real.mul_rpow ha hs (z := z)
    rw [Finset.prod_insert has, Finset.prod_insert has, hmul, ih hsub]

private lemma e30_coeff_norm_le (a : ℕ → ℂ) (c : ℝ)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c))
    (n : ℕ) (hn : n ≠ 0) :
    ‖chapter5Entry30Coeff a n‖ ≤ Real.rpow (n : ℝ) (-c) := by
  by_cases hsq : Squarefree n
  · rw [chapter5Entry30Coeff_of_squarefree a n hn hsq]
    have hprod : ∏ p ∈ n.primeFactors, p = n :=
      Nat.prod_primeFactors_of_squarefree hsq
    have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ)
        = ∏ p ∈ n.primeFactors, (p : ℝ) := Nat.cast_prod _ _
    have hrpow : Real.rpow (∏ p ∈ n.primeFactors, (p : ℝ)) (-c)
        = ∏ p ∈ n.primeFactors, Real.rpow (p : ℝ) (-c) :=
      e30_rpow_prod _ _ (fun i _ => Nat.cast_nonneg _) _
    calc ‖∏ p ∈ n.primeFactors, a p‖
        ≤ ∏ p ∈ n.primeFactors, ‖a p‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ p ∈ n.primeFactors, Real.rpow (p : ℝ) (-c) := by
          apply Finset.prod_le_prod₀
          · intro i hi; exact norm_nonneg _
          · intro i hi
            exact ha i (Nat.mem_primeFactors.mp hi).1
      _ = Real.rpow (n : ℝ) (-c) := by
          rw [← hrpow, ← hcast, hprod]
  · rw [chapter5Entry30Coeff_of_not_squarefree a n hn hsq, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private lemma e30_summable_rpow {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => Real.rpow (n : ℝ) (-c)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ c)⁻¹) :=
    (Real.summable_nat_rpow_inv (p := c)).mpr hc
  refine Summable.congr h (fun n => ?_)
  rw [← Real.rpow_neg (Nat.cast_nonneg n)]
  rfl

private lemma e30_summable_shift_two {c : ℝ} (hc : 1 < c) :
    Summable (fun j : ℕ => Real.rpow ((j + 2 : ℕ) : ℝ) (-c)) := by
  have h := e30_summable_rpow hc
  have h2 := (summable_nat_add_iff (G := ℝ) 2).mpr h
  simpa using h2

/-- **Summability of the Entry 30 coefficients.** Let $a : \mathbb{N} \to \mathbb{C}$ and let
$c > 1$ be real with $|a(p)| \le p^{-c}$ for every prime $p$. Then the Entry 30 coefficients
$f_a(n)$ of $a$ (equal to $0$ at $n = 0$; for $n \ge 1$, the product of $a(p)$ over the primes
$p \mid n$ if $n$ is squarefree, and $0$ otherwise) form a summable family over $n \ge 2$. -/
lemma summable_chapter5Entry30Coeff_add_two (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) := by
  apply Summable.of_norm_bounded (e30_summable_shift_two hc)
  intro j
  have hn : (j + 2) ≠ 0 := by omega
  have h := e30_coeff_norm_le a c ha (j + 2) hn
  simpa using h

/-- The coefficient at `0` is `0`. -/
@[simp]
lemma chapter5Entry30Coeff_zero (a : ℕ → ℂ) : chapter5Entry30Coeff a 0 = 0 := by
  unfold chapter5Entry30Coeff
  simp

/-- The coefficient at `1` is `1`. -/
@[simp]
lemma chapter5Entry30Coeff_one (a : ℕ → ℂ) : chapter5Entry30Coeff a 1 = 1 := by
  unfold chapter5Entry30Coeff
  simp

/-- At a prime `p`, the coefficient is `a p`. -/
lemma chapter5Entry30Coeff_prime (a : ℕ → ℂ) (p : ℕ) (hp : p.Prime) :
    chapter5Entry30Coeff a p = a p := by
  have hn : p ≠ 0 := hp.ne_zero
  have hsq : Squarefree p := hp.prime.squarefree
  rw [chapter5Entry30Coeff_of_squarefree a p hn hsq]
  have hpf : p.primeFactors = {p} := by
    have h1 : (p ^ 1).primeFactors = {p} :=
      Nat.primeFactors_prime_pow one_ne_zero hp
    simpa using h1
  rw [hpf]
  simp

/-- **Entry 30 coefficients vanish at higher prime powers.** For every function
$a : \mathbb{N} \to \mathbb{C}$, every prime $p$ and every $e \ge 2$, the Entry 30 coefficient
satisfies $c_a(p^e) = 0$. -/
lemma chapter5Entry30Coeff_prime_pow_of_two_le (a : ℕ → ℂ) (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    chapter5Entry30Coeff a (p ^ e) = 0 := by
  have hne : (p ^ e) ≠ 0 := pow_ne_zero e hp.ne_zero
  have hnsq : ¬Squarefree (p ^ e) := by
    intro hsq
    have hle := (Nat.squarefree_iff_factorization_le_one hne).mp hsq p
    have hfact : (p ^ e).factorization p = e := by
      rw [Nat.factorization_pow]
      simp [hp.factorization_self]
    omega
  exact chapter5Entry30Coeff_of_not_squarefree a _ hne hnsq

/-- **Entry 30 coefficients are multiplicative.** For every function $a : \mathbb{N} \to \mathbb{C}$
and all coprime $m, n \in \mathbb{N}$, the Entry 30 coefficients $c_a$ satisfy
$c_a(mn) = c_a(m)\,c_a(n)$. -/
lemma chapter5Entry30Coeff_mul_of_coprime (a : ℕ → ℂ) (m n : ℕ) (hcop : Nat.Coprime m n) :
    chapter5Entry30Coeff a (m * n) = chapter5Entry30Coeff a m * chapter5Entry30Coeff a n := by
  by_cases hm : m = 0
  · subst hm
    rw [Nat.coprime_zero_left] at hcop
    subst hcop
    simp [chapter5Entry30Coeff_zero, chapter5Entry30Coeff_one]
  · by_cases hn : n = 0
    · subst hn
      rw [Nat.coprime_zero_right] at hcop
      subst hcop
      simp [chapter5Entry30Coeff_zero, chapter5Entry30Coeff_one]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      by_cases hsq : Squarefree (m * n)
      · have hsqm : Squarefree m := Squarefree.of_mul_left hsq
        have hsqn : Squarefree n := Squarefree.of_mul_right hsq
        rw [chapter5Entry30Coeff_of_squarefree a _ hmn hsq,
          chapter5Entry30Coeff_of_squarefree a m hm hsqm,
          chapter5Entry30Coeff_of_squarefree a n hn hsqn]
        rw [Nat.primeFactors_mul hm hn]
        rw [Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
      · have h : ¬(Squarefree m ∧ Squarefree n) := by
          intro ⟨hsm, hsn⟩
          apply hsq
          rw [Nat.squarefree_mul_iff]
          exact ⟨hcop, hsm, hsn⟩
        by_cases hsm : Squarefree m
        · have hsn : ¬Squarefree n := fun hs => h ⟨hsm, hs⟩
          rw [chapter5Entry30Coeff_of_not_squarefree a _ hmn hsq,
            chapter5Entry30Coeff_of_not_squarefree a n hn hsn]
          simp
        · rw [chapter5Entry30Coeff_of_not_squarefree a _ hmn hsq,
            chapter5Entry30Coeff_of_not_squarefree a m hm hsm]
          simp

private lemma e30_norm_summable (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun n : ℕ => ‖chapter5Entry30Coeff a n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (e30_summable_rpow hc)
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [chapter5Entry30Coeff_zero, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact e30_coeff_norm_le a c ha n hn

private lemma e30_tsum_coeff_eq (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    (∑' n : ℕ, chapter5Entry30Coeff a n) = 1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2) := by
  have hsumm : Summable (chapter5Entry30Coeff a) :=
    (e30_norm_summable a c hc ha).of_norm
  have hshift1 := hsumm.tsum_eq_zero_add
  have g_summ : Summable (fun n : ℕ => chapter5Entry30Coeff a (n + 1)) :=
    (summable_nat_add_iff (G := ℂ) 1).mpr hsumm
  have hshift2 := g_summ.tsum_eq_zero_add
  have h0 : chapter5Entry30Coeff a 0 = 0 := chapter5Entry30Coeff_zero a
  have h1 : chapter5Entry30Coeff a (0 + 1) = 1 := by
    have : (0 + 1 : ℕ) = 1 := rfl
    rw [this]
    exact chapter5Entry30Coeff_one a
  have htail : (fun n : ℕ => chapter5Entry30Coeff a ((n + 1) + 1))
      = (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) := by
    funext n
    have heq : (n + 1) + 1 = n + 2 := by omega
    rw [heq]
  rw [h0] at hshift1
  rw [h1] at hshift2
  rw [htail] at hshift2
  have hmid : (∑' b : ℕ, chapter5Entry30Coeff a (b + 1))
      = 1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2) := hshift2
  rw [hmid] at hshift1
  simpa using hshift1

private lemma e30_tsum_prime_pow (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c))
    (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, chapter5Entry30Coeff a (p ^ e)) = 1 + a p := by
  have hsumm_all : Summable (chapter5Entry30Coeff a) :=
    (e30_norm_summable a c hc ha).of_norm
  have hp2 : 2 ≤ p := hp.two_le
  have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp2
  have hsumm : Summable (fun e : ℕ => chapter5Entry30Coeff a (p ^ e)) :=
    hsumm_all.comp_injective hinj
  have hvanish : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
      chapter5Entry30Coeff a (p ^ e) = 0 := by
    intro e he
    have he01 : e ≠ 0 ∧ e ≠ 1 := by
      simpa using he
    have he2 : 2 ≤ e := by omega
    exact chapter5Entry30Coeff_prime_pow_of_two_le a p e hp he2
  have hHasSum : HasSum (fun e : ℕ => chapter5Entry30Coeff a (p ^ e))
      (∑ e ∈ ({0, 1} : Finset ℕ), chapter5Entry30Coeff a (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hsum_eq : (∑ e ∈ ({0, 1} : Finset ℕ), chapter5Entry30Coeff a (p ^ e))
      = 1 + a p := by
    rw [Finset.sum_pair (by decide)]
    have e0 : p ^ (0 : ℕ) = 1 := pow_zero p
    have e1 : p ^ (1 : ℕ) = p := pow_one p
    rw [e0, e1, chapter5Entry30Coeff_one, chapter5Entry30Coeff_prime a p hp]
  rw [hsum_eq] at hHasSum
  exact HasSum.unique hsumm.hasSum hHasSum

/-- **Euler product for the Entry 30 coefficients.** Let $a : \mathbb{N} \to \mathbb{C}$ and let
$c > 1$ be real with $|a(p)| \le p^{-c}$ for every prime $p$. Write $f_a(n)$ for the Entry 30
coefficient of $a$ at $n$ (it is $0$ at $n = 0$; for $n \ge 1$ it is the product of $a(p)$ over
the primes $p \mid n$ if $n$ is squarefree, and $0$ otherwise). Then the product of $1 + a(p)$
over all primes $p$ converges unconditionally to $1 + \sum_{n \ge 2} f_a(n)$. -/
lemma hasProd_one_add_chapter5Entry30Coeff (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    HasProd (fun p : Nat.Primes => 1 + a p)
      (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2)) := by
  have hnorm_summ := e30_norm_summable a c hc ha
  have hsumm_all : Summable (chapter5Entry30Coeff a) := hnorm_summ.of_norm
  have hmult : ∀ {m n : ℕ}, Nat.Coprime m n →
      chapter5Entry30Coeff a (m * n) =
        chapter5Entry30Coeff a m * chapter5Entry30Coeff a n :=
    fun {m n} h => chapter5Entry30Coeff_mul_of_coprime a m n h
  have hEP := EulerProduct.eulerProduct_hasProd (f := chapter5Entry30Coeff a)
    (chapter5Entry30Coeff_one a) hmult hnorm_summ (chapter5Entry30Coeff_zero a)
  have hfac : ∀ q : Nat.Primes,
      (∑' e : ℕ, chapter5Entry30Coeff a (((q : ℕ)) ^ e)) = 1 + a ((q : ℕ)) :=
    fun q => e30_tsum_prime_pow a c hc ha _ q.property
  have htsum := e30_tsum_coeff_eq a c hc ha
  have hEP2 := HasProd.congr_fun hEP (fun q => (hfac q).symm)
  rw [htsum] at hEP2
  exact hEP2

private lemma e30_part1 (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) ∧
      (∀ n : ℕ, n ≠ 0 →
        chapter5Entry30Coeff a n =
          if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0) ∧
      HasProd (fun p : Nat.Primes => 1 + a p)
        (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2)) :=
  ⟨summable_chapter5Entry30Coeff_add_two a c hc ha, chapter5Entry30Coeff_of_ne_zero a,
    hasProd_one_add_chapter5Entry30Coeff a c hc ha⟩

private lemma e30_cpow_nat_mul (m n : ℕ) (z : ℂ) :
    ((((m * n : ℕ))) : ℂ) ^ z = ((m : ℂ)) ^ z * ((n : ℂ)) ^ z := by
  rw [← Complex.ofReal_natCast (m * n), ← Complex.ofReal_natCast m,
    ← Complex.ofReal_natCast n, Nat.cast_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) z

private lemma e30_norm_cpow_nat (n : ℕ) (s : ℂ) (hs : s.re ≠ 0) :
    ‖((n : ℂ)) ^ (-s)‖ = Real.rpow (n : ℝ) (-s.re) := by
  have hbase : ((n : ℂ)) = (((n : ℝ)) : ℂ) := (Complex.ofReal_natCast n).symm
  rw [hbase]
  have hne : (-s).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr hs
  have h := Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) hne
  simpa using h

private lemma e30_one_div_cpow_eq (n : ℕ) (s : ℂ) :
    1 / ((n : ℂ) ^ s) = ((n : ℂ) ^ (-s)) := by
  rw [one_div, ← Complex.cpow_neg]

private lemma e30_cpow_one (s : ℂ) : ((1 : ℕ) : ℂ) ^ (-s) = 1 := by
  simp

private def e30Fplus (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else if Squarefree n then (n : ℂ) ^ (-s) else 0

private lemma e30Fplus_zero (s : ℂ) : e30Fplus s 0 = 0 := by
  unfold e30Fplus
  simp

private lemma e30Fplus_one (s : ℂ) : e30Fplus s 1 = 1 := by
  unfold e30Fplus
  simp

private lemma e30Fplus_mult (s : ℂ) (m n : ℕ) (hcop : Nat.Coprime m n) :
    e30Fplus s (m * n) = e30Fplus s m * e30Fplus s n := by
  unfold e30Fplus
  by_cases hm : m = 0
  · subst hm
    rw [Nat.coprime_zero_left] at hcop
    subst hcop
    simp
  · by_cases hn : n = 0
    · subst hn
      rw [Nat.coprime_zero_right] at hcop
      subst hcop
      simp
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      simp only [hm, hn, hmn, ↓reduceIte]
      by_cases hsq : Squarefree (m * n)
      · have hsqm : Squarefree m := Squarefree.of_mul_left hsq
        have hsqn : Squarefree n := Squarefree.of_mul_right hsq
        simp only [hsq, hsqm, hsqn, ↓reduceIte]
        exact e30_cpow_nat_mul m n (-s)
      · have h : ¬(Squarefree m ∧ Squarefree n) := by
          intro ⟨hsm, hsn⟩
          apply hsq
          rw [Nat.squarefree_mul_iff]
          exact ⟨hcop, hsm, hsn⟩
        by_cases hsm : Squarefree m
        · have hsn : ¬Squarefree n := fun hs => h ⟨hsm, hs⟩
          simp [hsq, hsn]
        · simp [hsq, hsm]

private lemma e30Fplus_norm_le (s : ℂ) (hs : 1 < s.re) (n : ℕ) (hn : n ≠ 0) :
    ‖e30Fplus s n‖ ≤ Real.rpow (n : ℝ) (-s.re) := by
  unfold e30Fplus
  simp only [hn, ↓reduceIte]
  by_cases hsq : Squarefree n
  · simp only [hsq, ↓reduceIte]
    have hsne : s.re ≠ 0 := by
      intro hcon
      linarith
    exact (e30_norm_cpow_nat n s hsne).le
  · simp only [hsq, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _

private lemma e30_summable_Fplus_norm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖e30Fplus s n‖) := by
  have hbase : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-s.re)) :=
    e30_summable_rpow hs
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hbase
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [e30Fplus_zero, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact e30Fplus_norm_le s hs n hn

private lemma e30Fplus_prime_pow_ge_two (s : ℂ) (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    e30Fplus s (p ^ e) = 0 := by
  have hne : (p ^ e) ≠ 0 := pow_ne_zero e hp.ne_zero
  have hnsq : ¬Squarefree (p ^ e) := by
    intro hsq
    have hle := (Nat.squarefree_iff_factorization_le_one hne).mp hsq p
    have hfact : (p ^ e).factorization p = e := by
      rw [Nat.factorization_pow]
      simp [hp.factorization_self]
    omega
  unfold e30Fplus
  simp [hnsq]

private lemma e30Fplus_prime (s : ℂ) (p : ℕ) (hp : p.Prime) :
    e30Fplus s p = ((p : ℂ) ^ (-s)) := by
  unfold e30Fplus
  have hn : p ≠ 0 := hp.ne_zero
  have hsq : Squarefree p := hp.prime.squarefree
  simp [hn, hsq]

private lemma e30_tsum_Fplus_prime_pow (s : ℂ) (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, e30Fplus s (p ^ e)) = 1 + ((p : ℂ) ^ (-s)) := by
  have hsumm : Summable (e30Fplus s) := (e30_summable_Fplus_norm s hs).of_norm
  have hp2 : 2 ≤ p := hp.two_le
  have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp2
  have hsummc : Summable (fun e : ℕ => e30Fplus s (p ^ e)) :=
    hsumm.comp_injective hinj
  have hvanish : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
      e30Fplus s (p ^ e) = 0 := by
    intro e he
    have he01 : e ≠ 0 ∧ e ≠ 1 := by
      simpa using he
    have he2 : 2 ≤ e := by omega
    exact e30Fplus_prime_pow_ge_two s p e hp he2
  have hHasSum : HasSum (fun e : ℕ => e30Fplus s (p ^ e))
      (∑ e ∈ ({0, 1} : Finset ℕ), e30Fplus s (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hsum_eq : (∑ e ∈ ({0, 1} : Finset ℕ), e30Fplus s (p ^ e))
      = 1 + ((p : ℂ) ^ (-s)) := by
    rw [Finset.sum_pair (by decide)]
    have e0 : p ^ (0 : ℕ) = 1 := pow_zero p
    have e1 : p ^ (1 : ℕ) = p := pow_one p
    have h0 : e30Fplus s (p ^ (0 : ℕ)) = 1 := by
      rw [e0]; exact e30Fplus_one s
    have h1 : e30Fplus s (p ^ (1 : ℕ)) = ((p : ℂ) ^ (-s)) := by
      rw [e1]; exact e30Fplus_prime s p hp
    change e30Fplus s (p ^ (0 : ℕ)) + e30Fplus s (p ^ (1 : ℕ)) = _
    rw [h0, h1]
  rw [hsum_eq] at hHasSum
  exact HasSum.unique hsummc.hasSum hHasSum

private lemma e30_Fplus_shift (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fplus s n)
      = ∑' j : ℕ, (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  have hsumm : Summable (e30Fplus s) := (e30_summable_Fplus_norm s hs).of_norm
  have hshift := hsumm.tsum_eq_zero_add
  have h0 : e30Fplus s 0 = 0 := e30Fplus_zero s
  rw [h0, zero_add] at hshift
  have hpt : ∀ b : ℕ, e30Fplus s (b + 1)
      = (if Squarefree (b + 1) then (((b + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
    intro b
    unfold e30Fplus
    simp
  rw [hshift]
  exact tsum_congr hpt

private lemma e30_two_mul_re (s : ℂ) : (2 * s).re = 2 * s.re := by
  have h2 : (2 : ℂ) * s = s + s := by ring
  rw [h2, Complex.add_re]
  ring

private lemma e30_cpow_two_mul (p : ℕ) (s : ℂ) (hp0 : ((p : ℂ)) ≠ 0) :
    ((p : ℂ) ^ (-(2 * s))) = (((p : ℂ) ^ (-s)) ^ 2) := by
  have h2 : (2 : ℂ) * s = s + s := by ring
  have hadd : ((p : ℂ) ^ (-(s + s))) = ((p : ℂ) ^ (-s)) * ((p : ℂ) ^ (-s)) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [h2] at *
  rw [hadd, pow_two]

private lemma e30_norm_prime_cpow_lt_one (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℂ) ^ (-s))‖ < 1 := by
  have hsne : s.re ≠ 0 := by
    intro hcon; linarith
  rw [e30_norm_cpow_nat p s hsne]
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have h2 : 2 ≤ p := hp.two_le
    have hc : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith
  have hneg : -s.re < 0 := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hneg

private lemma e30_Splus_eq (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fplus s n) = riemannZeta s / riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz2ne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  have hnorm_summ := e30_summable_Fplus_norm s hs
  have hsumm : Summable (e30Fplus s) := hnorm_summ.of_norm
  have hmult : ∀ {m n : ℕ}, Nat.Coprime m n →
      e30Fplus s (m * n) = e30Fplus s m * e30Fplus s n :=
    fun {m n} h => e30Fplus_mult s m n h
  have hEP := EulerProduct.eulerProduct_hasProd (f := e30Fplus s)
    (e30Fplus_one s) hmult hnorm_summ (e30Fplus_zero s)
  have hfac : ∀ q : Nat.Primes,
      (∑' e : ℕ, e30Fplus s (((q : ℕ)) ^ e)) = 1 + (((q : ℕ) : ℂ) ^ (-s)) :=
    fun q => e30_tsum_Fplus_prime_pow s hs _ q.property
  have hEP2 := HasProd.congr_fun hEP (fun q => (hfac q).symm)
  have hZ := riemannZeta_eulerProduct_hasProd (s := s) hs
  have hZ2 := riemannZeta_eulerProduct_hasProd (s := 2 * s) h2re
  have hMul := hEP2.mul hZ2
  have hpt : ∀ q : Nat.Primes,
      (1 + (((q : ℕ) : ℂ) ^ (-s))) * (1 - (((q : ℕ) : ℂ) ^ (-(2 * s))))⁻¹
        = (1 - (((q : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro q
    set pn : ℕ := ((q : ℕ)) with hpn
    have hp : pn.Prime := q.property
    have hp0 : ((pn : ℂ)) ≠ 0 := by
      have hne : pn ≠ 0 := hp.ne_zero
      exact Nat.cast_ne_zero.mpr hne
    set x : ℂ := ((pn : ℂ) ^ (-s)) with hx
    set y : ℂ := ((pn : ℂ) ^ (-(2 * s))) with hy
    have hy_eq : y = x ^ 2 := by
      rw [hy, hx]
      exact e30_cpow_two_mul pn s hp0
    have hnx : ‖x‖ < 1 := e30_norm_prime_cpow_lt_one pn hp s hs
    have hny : ‖y‖ < 1 := by
      have hsne2 : (2 * s).re ≠ 0 := by
        intro hcon
        rw [e30_two_mul_re] at hcon
        have : s.re = 0 := by linarith
        linarith
      have hnormy : ‖y‖ = Real.rpow (pn : ℝ) (-(2 * s).re) := by
        rw [hy]
        exact e30_norm_cpow_nat pn (2 * s) hsne2
      rw [hnormy]
      have hp1 : (1 : ℝ) < (pn : ℝ) := by
        have h2 : 2 ≤ pn := hp.two_le
        have hc : (2 : ℝ) ≤ (pn : ℝ) := by exact_mod_cast h2
        linarith
      have hneg : -(2 * s).re < 0 := by
        have : (2 * s).re = 2 * s.re := e30_two_mul_re s
        linarith
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hneg
    have h1x : (1 : ℂ) - x ≠ 0 := by
      intro hcon
      have hx1 : x = 1 := (sub_eq_zero.mp hcon).symm
      have h1 : ‖x‖ = 1 := by rw [hx1, norm_one]
      linarith
    have h1px : (1 : ℂ) + x ≠ 0 := by
      intro hcon
      have hxm1 : x = -1 := by linear_combination hcon
      have h1 : ‖x‖ = 1 := by rw [hxm1, norm_neg, norm_one]
      linarith
    have h1y : (1 : ℂ) - y ≠ 0 := by
      intro hcon
      have hy1 : y = 1 := (sub_eq_zero.mp hcon).symm
      have h1 : ‖y‖ = 1 := by rw [hy1, norm_one]
      linarith
    have hfactor : (1 : ℂ) - y = (1 - x) * (1 + x) := by
      rw [hy_eq]
      ring
    rw [hfactor, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ h1px, one_mul]
  have hMul2 := HasProd.congr_fun hMul (fun q => (hpt q).symm)
  have hEq : (∑' n : ℕ, e30Fplus s n) * riemannZeta (2 * s) = riemannZeta s :=
    HasProd.unique hMul2 hZ
  exact (eq_div_iff hz2ne).mpr hEq

/-- **Squarefree term, explicit form.** For $s \in \mathbb{C}$ and a natural number $j$, the $j$-th
term of the Dirichlet series over squarefree integers equals $(j + 1)^{-s}$ if $j + 1$ is
squarefree and $0$ otherwise. -/
lemma chapter5Entry30SquarefreeTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30SquarefreeTerm s j
      = (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  unfold chapter5Entry30SquarefreeTerm
  simp

private lemma e30_summable_shift_one {c : ℝ} (hc : 1 < c) :
    Summable (fun j : ℕ => Real.rpow ((j + 1 : ℕ) : ℝ) (-c)) := by
  have h := e30_summable_rpow hc
  have h1 := (summable_nat_add_iff (G := ℝ) 1).mpr h
  simpa using h1

private lemma e30_sq_term_Fplus (s : ℂ) (j : ℕ) :
    chapter5Entry30SquarefreeTerm s j = e30Fplus s (j + 1) := by
  rw [chapter5Entry30SquarefreeTerm_def s j]
  unfold e30Fplus
  simp

/-- **Summability of the squarefree terms.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the series of $n^{-s}$ over the squarefree $n \ge 1$ is summable. -/
lemma summable_chapter5Entry30SquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30SquarefreeTerm s) := by
  have hbound : Summable (fun j : ℕ => Real.rpow ((j + 1 : ℕ) : ℝ) (-s.re)) :=
    e30_summable_shift_one hs
  apply Summable.of_norm_bounded hbound
  intro j
  rw [e30_sq_term_Fplus s j]
  exact e30Fplus_norm_le s hs (j + 1) (by omega)

/-- **Sum of $n^{-s}$ over squarefree $n$.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the sum of $n^{-s}$ over the squarefree $n \ge 1$ equals
$\zeta(s)/\zeta(2s)$. -/
lemma tsum_chapter5Entry30SquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
      = riemannZeta s / riemannZeta (2 * s) := by
  have h1 : (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
      = (∑' j : ℕ, (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0)) :=
    tsum_congr (fun j => chapter5Entry30SquarefreeTerm_def s j)
  rw [h1, ← e30_Fplus_shift s hs]
  exact e30_Splus_eq s hs

private def e30Fmu (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℕ) : ℂ) ^ (-s))

private lemma e30Fmu_zero (s : ℂ) : e30Fmu s 0 = 0 := by
  unfold e30Fmu
  simp

private lemma e30_term_mu_eq (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n
      = e30Fmu s n := by
  unfold LSeries.term e30Fmu
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]

private lemma e30_Lmu_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fmu s n) = (riemannZeta s)⁻¹ := by
  have hsumable : LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff).mpr hs
  have hHasSum := hsumable.LSeriesHasSum
  have htsum_term : (∑' n : ℕ, LSeries.term _ s n)
      = LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    HasSum.tsum_eq hHasSum
  have hcongr : (∑' n : ℕ, e30Fmu s n)
      = (∑' n : ℕ, LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n) :=
    tsum_congr (fun n => (e30_term_mu_eq s n).symm)
  have hprod : LSeries 1 s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 :=
    LSeries_one_mul_Lseries_moebius hs
  have hL1 : LSeries 1 s = riemannZeta s := LSeries_one_eq_riemannZeta hs
  rw [hL1] at hprod
  have hLmu : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s
      = (riemannZeta s)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hcongr, htsum_term, hLmu]

private lemma e30_summable_Fmu (s : ℂ) (hs : 1 < s.re) : Summable (e30Fmu s) := by
  have hsumable : LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff).mpr hs
  exact Summable.congr hsumable (fun n => e30_term_mu_eq s n)

private lemma e30_Fmu_shift_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, e30Fmu s (j + 1)) = (riemannZeta s)⁻¹ := by
  have hsumm := e30_summable_Fmu s hs
  have hshift := hsumm.tsum_eq_zero_add
  rw [e30Fmu_zero s, zero_add, e30_Lmu_tsum s hs] at hshift
  exact hshift.symm

private lemma e30_mu_card (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    (((ArithmeticFunction.moebius n : ℤ)) : ℂ) = (-1 : ℂ) ^ (n.primeFactors.card) := by
  have hfact := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ArithmeticFunction.moebius ArithmeticFunction.isMultiplicative_moebius hn
  have hsupp : n.factorization.support = n.primeFactors := Nat.support_factorization n
  have hprod : n.factorization.prod (fun p k => ArithmeticFunction.moebius (p ^ k))
      = ∏ p ∈ n.primeFactors, (-1 : ℤ) := by
    have hunfold : n.factorization.prod (fun p k => ArithmeticFunction.moebius (p ^ k))
        = ∏ p ∈ n.factorization.support,
          ArithmeticFunction.moebius (p ^ (n.factorization p)) := rfl
    rw [hunfold, hsupp]
    apply Finset.prod_congr rfl
    intro p hp
    have hpos : 0 < n.factorization p := by
      have hmem2 : p ∈ n.factorization.support := by
        rw [hsupp]; exact hp
      have hne := Finsupp.mem_support_iff.mp hmem2
      omega
    have hle : n.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
    have heq : n.factorization p = 1 := by omega
    have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    rw [heq, pow_one]
    exact ArithmeticFunction.moebius_apply_prime hprime
  have hmu : ArithmeticFunction.moebius n = ∏ p ∈ n.primeFactors, (-1 : ℤ) := by
    rw [hfact]
    exact hprod
  rw [hmu]
  push_cast
  rw [Finset.prod_const]

/-- **Odd-count squarefree term, explicit form.** For $s \in \mathbb{C}$ and a natural number $j$,
the $j$-th term of the Dirichlet series over squarefree integers with an odd number of prime
factors equals $(j + 1)^{-s}$ if $j + 1$ is squarefree and has an odd number of distinct prime
factors, and $0$ otherwise. -/
lemma chapter5Entry30OddTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30OddTerm s j
      = (if Squarefree (j + 1) ∧ Odd (j + 1).primeFactors.card
        then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  unfold chapter5Entry30OddTerm
  rfl

private lemma e30_odd_term_eq (s : ℂ) (j : ℕ) :
    chapter5Entry30OddTerm s j
      = (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2 := by
  have hn : (j + 1) ≠ 0 := by omega
  have hmu_t : e30Fmu s (j + 1)
      = ((ArithmeticFunction.moebius (j + 1) : ℤ) : ℂ) * ((((j + 1 : ℕ)) : ℂ) ^ (-s)) := by
    unfold e30Fmu
    simp
  rw [chapter5Entry30OddTerm_def s j, chapter5Entry30SquarefreeTerm_def s j, hmu_t]
  by_cases hsq : Squarefree (j + 1)
  · have hmu := e30_mu_card (j + 1) hn hsq
    by_cases hodd : Odd (j + 1).primeFactors.card
    · have hmu_neg : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = -1 := by
        rw [hmu]
        exact hodd.neg_one_pow
      simp only [hsq, hodd, and_true, ite_true, hmu_neg]
      ring
    · have heven : Even (j + 1).primeFactors.card := Nat.not_odd_iff_even.mp hodd
      have hmu_one : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = 1 := by
        rw [hmu]
        exact heven.neg_one_pow
      simp only [hsq, hodd, and_false, ite_true, ite_false, hmu_one]
      ring
  · have hmu0 : ArithmeticFunction.moebius (j + 1) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hmu0c : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = 0 := by
      rw [hmu0]
      simp
    simp only [hsq, false_and, ite_false, hmu0c]
    ring

private lemma e30_summable_Fmu_shift (s : ℂ) (hs : 1 < s.re) :
    Summable (fun j : ℕ => e30Fmu s (j + 1)) :=
  (summable_nat_add_iff (G := ℂ) 1).mpr (e30_summable_Fmu s hs)

/-- **Summability of the odd squarefree terms.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the series of $n^{-s}$ over the squarefree $n \ge 1$ with an odd number
of distinct prime factors is summable. -/
lemma summable_chapter5Entry30OddTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30OddTerm s) := by
  have hRHS : Summable (fun j : ℕ =>
      (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2) := by
    have hsub := (summable_chapter5Entry30SquarefreeTerm s hs).sub (e30_summable_Fmu_shift s hs)
    have heq : ∀ j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2
        = (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹ := by
      intro j
      rw [div_eq_mul_inv]
    have hmul := hsub.mul_right ((2 : ℂ)⁻¹)
    exact Summable.congr hmul (fun j => (heq j).symm)
  exact Summable.congr hRHS (fun j => (e30_odd_term_eq s j).symm)

private lemma e30_odd_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = ((∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
        - (∑' j : ℕ, e30Fmu s (j + 1))) / 2 := by
  have hsub := (summable_chapter5Entry30SquarefreeTerm s hs).sub (e30_summable_Fmu_shift s hs)
  have htsub : (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)))
      = (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
        - (∑' j : ℕ, e30Fmu s (j + 1)) :=
    Summable.tsum_sub (summable_chapter5Entry30SquarefreeTerm s hs) (e30_summable_Fmu_shift s hs)
  have hmul_tsum : (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹)
      = (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1))) * (2 : ℂ)⁻¹ :=
    hsub.tsum_mul_right _
  have hcongr1 : (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2) :=
    tsum_congr (fun j => e30_odd_term_eq s j)
  have hcongr2 : (fun j : ℕ => (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2)
      = (fun j : ℕ => (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹) := by
    funext j
    rw [div_eq_mul_inv]
  rw [hcongr1, hcongr2, hmul_tsum, htsub, div_eq_mul_inv]

/-- **Sum of $n^{-s}$ over squarefree $n$ with an odd number of prime factors.** For every complex
number $s$ with $\operatorname{Re} s > 1$, the sum of $n^{-s}$ over the squarefree $n \ge 1$ with
an odd number of distinct prime factors equals $(\zeta(s)^2 - \zeta(2s))/(2\zeta(s)\zeta(2s))$. -/
lemma tsum_chapter5Entry30OddTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
        (2 * riemannZeta s * riemannZeta (2 * s)) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [e30_odd_tsum s hs, tsum_chapter5Entry30SquarefreeTerm s hs, e30_Fmu_shift_tsum s hs]
  field_simp

private lemma e30_summable_cpow (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n : ℕ)) : ℂ) ^ (-s)) := by
  apply Summable.of_norm_bounded (e30_summable_rpow hs)
  intro n
  by_cases hn : n = 0
  · subst hn
    have hcast : ((((0 : ℕ))) : ℂ) = (0 : ℂ) := Nat.cast_zero
    have hns : (-s) ≠ 0 := by
      intro hcon
      have hre : (-s).re = 0 := by rw [hcon]; rfl
      rw [Complex.neg_re] at hre
      have hsne : s.re ≠ 0 := by
        intro hcon2; linarith
      exact hsne (by linarith)
    have h0 : ((((0 : ℕ))) : ℂ) ^ (-s) = 0 := by
      rw [hcast, Complex.zero_cpow hns]
    rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hsne : s.re ≠ 0 := by
      intro hcon; linarith
    rw [e30_norm_cpow_nat n s hsne]

private lemma e30_cpow_shift_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, ((((j + 1 : ℕ)) : ℂ) ^ (-s))) = riemannZeta s := by
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℕ) : ℂ) ^ s :=
    zeta_eq_tsum_one_div_nat_cpow hs
  have hcongr : (∑' n : ℕ, 1 / ((n : ℕ) : ℂ) ^ s)
      = (∑' n : ℕ, (((n : ℕ)) : ℂ) ^ (-s)) :=
    tsum_congr (fun n => e30_one_div_cpow_eq n s)
  have hsumm := e30_summable_cpow s hs
  have hshift := hsumm.tsum_eq_zero_add
  have hsne : s ≠ 0 := by
    intro hcon
    rw [hcon, Complex.zero_re] at hs
    linarith
  have hns : (-s) ≠ 0 := neg_ne_zero.mpr hsne
  have h0 : ((((0 : ℕ))) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow hns]
  rw [h0, zero_add] at hshift
  rw [hz, hcongr] at *
  exact hshift.symm

/-- **Non-squarefree term, explicit form.** For $s \in \mathbb{C}$ and a natural number $j$, the
$j$-th term of the Dirichlet series over non-squarefree integers equals $0$ if $j + 1$ is
squarefree and $(j + 1)^{-s}$ otherwise. -/
lemma chapter5Entry30NonSquarefreeTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30NonSquarefreeTerm s j
      = (if Squarefree (j + 1) then 0 else ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
  unfold chapter5Entry30NonSquarefreeTerm
  rfl

private lemma e30_nsq_term_eq (s : ℂ) (j : ℕ) :
    chapter5Entry30NonSquarefreeTerm s j
      = ((((j + 1 : ℕ))) : ℂ) ^ (-s) - chapter5Entry30SquarefreeTerm s j := by
  rw [chapter5Entry30NonSquarefreeTerm_def s j, chapter5Entry30SquarefreeTerm_def s j]
  by_cases hsq : Squarefree (j + 1)
  · simp only [hsq, ite_true]
    ring
  · simp only [hsq, ite_false]
    ring

/-- **Summability of the non-squarefree terms.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the series of $n^{-s}$ over the non-squarefree $n \ge 1$ is summable. -/
lemma summable_chapter5Entry30NonSquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30NonSquarefreeTerm s) := by
  have hcpow_shift : Summable (fun j : ℕ => ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
    have h := e30_summable_cpow s hs
    have h1 := (summable_nat_add_iff (G := ℂ) 1).mpr h
    simpa using h1
  have hsub := hcpow_shift.sub (summable_chapter5Entry30SquarefreeTerm s hs)
  exact Summable.congr hsub (fun j => (e30_nsq_term_eq s j).symm)

private lemma e30_nsq_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = (∑' j : ℕ, ((((j + 1 : ℕ))) : ℂ) ^ (-s))
        - (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) := by
  have hcpow_shift : Summable (fun j : ℕ => ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
    have h := e30_summable_cpow s hs
    have h1 := (summable_nat_add_iff (G := ℂ) 1).mpr h
    simpa using h1
  have hcongr : (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = (∑' j : ℕ, (((((j + 1 : ℕ))) : ℂ) ^ (-s) - chapter5Entry30SquarefreeTerm s j)) :=
    tsum_congr (fun j => e30_nsq_term_eq s j)
  rw [hcongr]
  exact Summable.tsum_sub hcpow_shift (summable_chapter5Entry30SquarefreeTerm s hs)

/-- **Sum of $n^{-s}$ over non-squarefree $n$.** For every complex number $s$ with
$\operatorname{Re} s > 1$, the sum of $n^{-s}$ over the non-squarefree $n \ge 1$ equals
$\zeta(s)(\zeta(2s) - 1)/\zeta(2s)$. -/
lemma tsum_chapter5Entry30NonSquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = riemannZeta s * (riemannZeta (2 * s) - 1) / riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [e30_nsq_tsum s hs, e30_cpow_shift_tsum s hs, tsum_chapter5Entry30SquarefreeTerm s hs]
  field_simp

private lemma e30_cpow_nat_prod (s : Finset ℕ) (f : ℕ → ℕ) (z : ℂ) :
    ((((∏ i ∈ s, f i : ℕ))) : ℂ) ^ z = ∏ i ∈ s, ((((f i : ℕ))) : ℂ) ^ z := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a t has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hmul := e30_cpow_nat_mul (f a) (∏ i ∈ t, f i) z
    rw [hmul]
    rw [ih]

/-- **Explicit form of the signed coefficient.** For $s \in \mathbb{C}$ and a natural number
$n \ne 0$, the signed coefficient of $n$ equals $-n^{-s}$ if $n$ is squarefree with an odd number
of distinct prime factors, $n^{-s}$ if $n$ is squarefree with an even number of distinct prime
factors, and $0$ if $n$ is not squarefree. -/
lemma chapter5Entry30SignedCoeff_of_ne_zero (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    chapter5Entry30SignedCoeff s n =
      if Squarefree n then
        if Odd n.primeFactors.card then -((((n : ℕ))) : ℂ) ^ (-s)
        else ((((n : ℕ))) : ℂ) ^ (-s)
      else 0 := by
  have hchar := chapter5Entry30Coeff_of_ne_zero (fun p : ℕ => -((((p : ℕ))) : ℂ) ^ (-s)) n hn
  unfold chapter5Entry30SignedCoeff
  rw [hchar]
  by_cases hsq : Squarefree n
  · simp only [hsq, ite_true]
    have hprod_cpow : (∏ p ∈ n.primeFactors, ((((p : ℕ))) : ℂ) ^ (-s))
        = ((((n : ℕ))) : ℂ) ^ (-s) := by
      have hprod_nat : ∏ p ∈ n.primeFactors, p = n :=
        Nat.prod_primeFactors_of_squarefree hsq
      have hcpow := e30_cpow_nat_prod n.primeFactors (fun p => p) (-s)
      rw [hprod_nat] at hcpow
      exact hcpow.symm
    rw [Finset.prod_neg, hprod_cpow]
    by_cases hodd : Odd n.primeFactors.card
    · simp [hodd, hodd.neg_one_pow]
    · have heven : Even n.primeFactors.card := Nat.not_odd_iff_even.mp hodd
      simp [hodd, heven.neg_one_pow]
  · simp [hsq]

private lemma e30_part2 (s : ℂ) (hs : 1 < s.re) :
    (∀ n : ℕ, n ≠ 0 →
      chapter5Entry30SignedCoeff s n =
        if Squarefree n then
          if Odd n.primeFactors.card then -((((n : ℕ))) : ℂ) ^ (-s)
          else ((((n : ℕ))) : ℂ) ^ (-s)
        else 0) ∧
    riemannZeta s ≠ 0 ∧
    riemannZeta (2 * s) ≠ 0 ∧
    Summable (chapter5Entry30SquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
      riemannZeta s / riemannZeta (2 * s) ∧
    Summable (chapter5Entry30OddTerm s) ∧
    (∑' j : ℕ, chapter5Entry30OddTerm s j) =
      (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
        (2 * riemannZeta s * riemannZeta (2 * s)) ∧
    Summable (chapter5Entry30NonSquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
      riemannZeta s * (riemannZeta (2 * s) - 1) /
        riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  refine ⟨fun n hn => chapter5Entry30SignedCoeff_of_ne_zero s n hn, hz, hz2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact summable_chapter5Entry30SquarefreeTerm s hs
  · exact tsum_chapter5Entry30SquarefreeTerm s hs
  · exact summable_chapter5Entry30OddTerm s hs
  · exact tsum_chapter5Entry30OddTerm s hs
  · exact summable_chapter5Entry30NonSquarefreeTerm s hs
  · exact tsum_chapter5Entry30NonSquarefreeTerm s hs

/-- **Ramanujan's squarefree Dirichlet series (Entry 30).** (i) Let $a : \mathbb{N} \to \mathbb{C}$
and let $c > 1$ be real with $|a(p)| \le p^{-c}$ for every prime $p$, and write $f_a(n)$ for the
Entry 30 coefficient of $a$ at $n$. Then the family $(f_a(n))_{n \ge 2}$ is summable; for every
$n \ge 1$, $f_a(n)$ is the product of $a(p)$ over the primes $p \mid n$ if $n$ is squarefree and
$0$ otherwise; and the product of $1 + a(p)$ over all primes $p$ converges unconditionally to
$1 + \sum_{n \ge 2} f_a(n)$. (ii) Let $s$ be a complex number with $\operatorname{Re} s > 1$.
Then for every $n \ge 1$ the Entry 30 coefficient at $n$ of $p \mapsto -p^{-s}$ is $-n^{-s}$ if
$n$ is squarefree with an odd number of distinct prime factors, $n^{-s}$ if $n$ is squarefree
with an even number of distinct prime factors, and $0$ if $n$ is not squarefree; $\zeta(s) \ne 0$
and $\zeta(2s) \ne 0$; the series of $n^{-s}$ over the squarefree $n \ge 1$ is summable with sum
$\zeta(s)/\zeta(2s)$; the series of $n^{-s}$ over the squarefree $n \ge 1$ with an odd number of
distinct prime factors is summable with sum $(\zeta(s)^2 - \zeta(2s))/(2\zeta(s)\zeta(2s))$; and
the series of $n^{-s}$ over the non-squarefree $n \ge 1$ is summable with sum
$\zeta(s)(\zeta(2s) - 1)/\zeta(2s)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5,
Entry 30, pp. 131–132.
Proves `Wanted` entry `ramanujan_part1_ch5_entry30_secondordereulerian`.
-/
theorem ramanujan_part1_ch5_entry30_secondordereulerian :
    (∀ (a : ℕ → ℂ) (c : ℝ), 1 < c →
      (∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) →
        Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) ∧
        (∀ n : ℕ, n ≠ 0 →
          chapter5Entry30Coeff a n =
            if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0) ∧
        HasProd (fun p : Nat.Primes => 1 + a p)
          (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2))) ∧
    (∀ s : ℂ, 1 < s.re →
      (∀ n : ℕ, n ≠ 0 →
        chapter5Entry30SignedCoeff s n =
          if Squarefree n then
            if Odd n.primeFactors.card then -((n : ℂ) ^ (-s))
            else (n : ℂ) ^ (-s)
          else 0) ∧
      riemannZeta s ≠ 0 ∧
      riemannZeta (2 * s) ≠ 0 ∧
      Summable (chapter5Entry30SquarefreeTerm s) ∧
      (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
        riemannZeta s / riemannZeta (2 * s) ∧
      Summable (chapter5Entry30OddTerm s) ∧
      (∑' j : ℕ, chapter5Entry30OddTerm s j) =
        (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
          (2 * riemannZeta s * riemannZeta (2 * s)) ∧
      Summable (chapter5Entry30NonSquarefreeTerm s) ∧
      (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
        riemannZeta s * (riemannZeta (2 * s) - 1) /
          riemannZeta (2 * s)) := by
  constructor
  · intro a c hc ha
    exact e30_part1 a c hc ha
  · intro s hs
    exact e30_part2 s hs

end

end Entry30Secondordereulerian

end MathlibExt.Analysis.Ramanujan.Part1Ch5
