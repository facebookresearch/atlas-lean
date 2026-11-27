/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius

/-!
# Weighted Dirichlet convolution of monic polynomials

This file defines Dirichlet convolution and its partial sums over monic polynomials,
and proves Camargo's identity for completely multiplicative functions.
-/

open Polynomial UniqueFactorizationMonoid

namespace MetaMathlibExt

@[expose] public section

/-- **Dirichlet convolution over monic divisors.** Let $F$ be a field. The Dirichlet convolution
of functions $\alpha$ and $\beta$ from $F[T]$ to $\mathbb{C}$ is the function $\alpha * \beta$
given at $f \in F[T]$ by
$$(\alpha * \beta)(f) = \sum_{g \text{ monic},\ g \mid f} \alpha(g)\, \beta(f/g),$$
the sum running over the monic divisors $g$ of $f$.

When $f = 0$ every monic polynomial divides $f$; the sum is then the sum of its nonzero terms if
there are finitely many, and $0$ otherwise.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public noncomputable def monicDirichletConv {F : Type*} [Field F] (α β : F[X] → ℂ)
    (f : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, α g * β (f /ₘ g)

/-- **Dirichlet convolution at $1$.** Let $F$ be a field and let $\alpha$ and $\beta$ be functions
from $F[T]$ to $\mathbb{C}$. Their Dirichlet convolution over monic divisors satisfies
$(\alpha * \beta)(1) = \alpha(1) \beta(1)$, since the only monic divisor of $1$ is $1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of the
Dirichlet convolution. -/
public theorem monicDirichletConv_one {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicDirichletConv α β 1 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ g ∣ 1} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hm, hg⟩
      exact hm.isUnit_iff.mp (isUnit_of_dvd_one hg)
    · rintro rfl
      exact ⟨monic_one, dvd_rfl⟩
  rw [monicDirichletConv, hset, finsum_mem_singleton, divByMonic_one]

/-- **Monic polynomials of degree zero.** Let $F$ be a field. A polynomial $f \in F[T]$ is monic
of degree at most $0$ if and only if $f = 1$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 2, the set
`M_{≤ 0}`. -/
public theorem monic_natDegree_le_zero_iff {F : Type*} [Field F] {f : F[X]} :
    f.Monic ∧ f.natDegree ≤ 0 ↔ f = 1 := by
  constructor
  · rintro ⟨hm, hd⟩
    exact eq_one_of_monic_natDegree_zero hm (Nat.le_zero.mp hd)
  · rintro rfl
    exact ⟨monic_one, by simp⟩

/-- **Partial sums of a Dirichlet convolution over monic polynomials.** Let $F$ be a field, let
$\alpha, \beta \colon F[T] \to \mathbb{C}$, and let $\alpha * \beta$ be their Dirichlet
convolution over monic divisors. For an integer $n$,
$D[\alpha, \beta](n) = \sum_g (\alpha * \beta)(g)$, the sum over the monic $g \in F[T]$ of degree
at most $n$. For $n < 0$ the sum is empty, so $D[\alpha, \beta](n) = 0$; this is how the paper's
Lemma 3 uses $D$ at $n - \deg(f \ell)$.

The sum is a finitary sum: it is $0$ when infinitely many of its terms are nonzero, which can
happen only for infinite $F$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public noncomputable def monicConvPartialSum {F : Type*} [Field F] (α β : F[X] → ℂ) (n : ℤ) : ℂ :=
  ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n}, monicDirichletConv α β g

/-- **$D[\alpha, \beta]$ vanishes at negative arguments.** Let $F$ be a field and let
$\alpha, \beta \colon F[T] \to \mathbb{C}$. For every integer $n < 0$, the partial sum of the
Dirichlet convolution of $\alpha$ and $\beta$ satisfies $D[\alpha, \beta](n) = 0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_of_neg {F : Type*} [Field F] (α β : F[X] → ℂ) {n : ℤ}
    (hn : n < 0) : monicConvPartialSum α β n = 0 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ n} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro _
    omega
  rw [monicConvPartialSum, hset, finsum_mem_empty]

/-- **The partial sum $D[\alpha, \beta](0)$.** Let $F$ be a field and let
$\alpha, \beta \colon F[T] \to \mathbb{C}$. The partial sum of the Dirichlet convolution of
$\alpha$ and $\beta$ at $0$ is $D[\alpha, \beta](0) = \alpha(1)\, \beta(1)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[α, β](n)`. -/
public theorem monicConvPartialSum_zero {F : Type*} [Field F] (α β : F[X] → ℂ) :
    monicConvPartialSum α β 0 = α 1 * β 1 := by
  have hset : {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ 0} = {1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    rw [← monic_natDegree_le_zero_iff]
    exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
  rw [monicConvPartialSum, hset, finsum_mem_singleton, monicDirichletConv_one]

/-- **Weighted convolution sum.** Let $F$ be a field, let $\gamma, \alpha, \beta$ be functions from
$F[T]$ to $\mathbb{C}$, and write $\alpha * \beta$ for the monic Dirichlet convolution of $\alpha$
and $\beta$. For a natural number $n$, let $M_{\le n}$ be the set of monic polynomials in $F[T]$ of
degree at most $n$. The weighted convolution sum is
$$D(\gamma, \alpha, \beta; n) = \sum_{f \in M_{\le n}} \gamma(f)\,(\alpha * \beta)(f).$$

When $F$ is infinite and this sum has infinitely many nonzero terms, its value is taken to be $0$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public noncomputable def weightedMonicConvSum {F : Type*} [Field F] (γ α β : F[X] → ℂ)
    (n : ℕ) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n}, γ f * monicDirichletConv α β f

/-- **The weighted convolution sum at degree zero.** Let $F$ be a field and let
$\gamma, \alpha, \beta$ be functions from $F[T]$ to $\mathbb{C}$, and write $\alpha * \beta$ for
the monic Dirichlet convolution. The weighted convolution sum $D(\gamma, \alpha, \beta; 0)$, the
sum of $\gamma(f)\,(\alpha * \beta)(f)$ over the monic $f \in F[T]$ of degree at most $0$, equals
$\gamma(1)\,\alpha(1)\,\beta(1)$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Section 3, definition of
`D[γ, α, β](n)`. -/
public theorem weightedMonicConvSum_zero {F : Type*} [Field F] (γ α β : F[X] → ℂ) :
    weightedMonicConvSum γ α β 0 = γ 1 * (α 1 * β 1) := by
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ 0} = {1} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact monic_natDegree_le_zero_iff
  rw [weightedMonicConvSum, hset, finsum_mem_singleton, monicDirichletConv_one]

end

namespace weightedMonicConvSum_eq_of_completelyMultiplicative

variable {F : Type*} [Field F]

private theorem mul_quotient {a b : F[X]} (ha : a.Monic) (hab : a ∣ b) :
    a * (b /ₘ a) = b := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_divByMonic_cancel_left _ ha]

private theorem monic_quotient {a b : F[X]} (ha : a.Monic) (hb : b.Monic) (hab : a ∣ b) :
    (b /ₘ a).Monic :=
  ha.of_mul_monic_left (by rwa [mul_quotient ha hab])

private theorem finite_monics [Finite F] (k : ℤ) :
    {g : F[X] | g.Monic ∧ (g.natDegree : ℤ) ≤ k}.Finite := by
  let : Finite (degreeLT F (k.toNat + 1)) :=
    Finite.of_injective _ (degreeLTEquiv F (k.toNat + 1)).injective
  refine ((degreeLT F (k.toNat + 1) : Set F[X]).toFinite).subset ?_
  intro g hg
  have h := hg.2
  exact mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast (show
    g.natDegree < k.toNat + 1 by omega)))

private noncomputable def monics [Finite F] (k : ℤ) : Finset F[X] :=
  (finite_monics k).toFinset

private theorem mem_monics [Finite F] {k : ℤ} {g : F[X]} :
    g ∈ monics k ↔ g.Monic ∧ (g.natDegree : ℤ) ≤ k := Set.Finite.mem_toFinset _

open Classical in
private noncomputable def divisors (f : F[X]) : Finset F[X] :=
  if hf : f = 0 then ∅ else
    letI := fintypeSubtypeMonicDvd f hf
    (Set.toFinite {g : F[X] | g.Monic ∧ g ∣ f}).toFinset

private theorem mem_divisors {f g : F[X]} (hf : f ≠ 0) :
    g ∈ divisors f ↔ g.Monic ∧ g ∣ f := by
  simp [divisors, hf]

private theorem finsum_divisors {f : F[X]} (hf : f ≠ 0) (w : F[X] → ℂ) :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ f}, w g = ∑ g ∈ divisors f, w g := by
  rw [divisors, dite_eq_right hf, finsum_mem_eq_finite_toFinset_sum]

private theorem conv_eq_sum (α β : F[X] → ℂ) {f : F[X]} (hf : f.Monic) :
    monicDirichletConv α β f = ∑ g ∈ divisors f, α g * β (f /ₘ g) :=
  finsum_divisors hf.ne_zero _

-- Multiplication by a monic divisor identifies divisors of the quotient with its multiples.
open Classical in
private theorem sum_divisors_mul {a f : F[X]} (ha : a.Monic) (hf : f.Monic) (haf : a ∣ f)
    (w : F[X] → ℂ) :
    ∑ g ∈ divisors (f /ₘ a), w g =
      ∑ g ∈ (divisors f).filter (a ∣ ·), w (g /ₘ a) := by
  have hq := mul_quotient ha haf
  apply Finset.sum_bij (fun g _ => a * g)
  · intro g hg
    obtain ⟨hm, hd⟩ := (mem_divisors (monic_quotient ha hf haf).ne_zero).mp hg
    exact Finset.mem_filter.mpr ⟨(mem_divisors hf.ne_zero).mpr
      ⟨ha.mul hm, hq ▸ mul_dvd_mul_left a hd⟩, dvd_mul_right a g⟩
  · exact fun _ _ _ _ h => mul_left_cancel₀ ha.ne_zero h
  · intro g hg
    obtain ⟨hg, hag⟩ := Finset.mem_filter.mp hg
    obtain ⟨hm, hd⟩ := (mem_divisors hf.ne_zero).mp hg
    have hgq := mul_quotient ha hag
    refine ⟨g /ₘ a, (mem_divisors (monic_quotient ha hf haf).ne_zero).mpr
      ⟨monic_quotient ha hm hag, ?_⟩, hgq⟩
    exact (mul_dvd_mul_iff_left ha.ne_zero).mp (hq.symm ▸ hgq.symm ▸ hd)
  · intro g _
    rw [mul_divByMonic_cancel_left _ ha]

-- Pair multiples of a prime with their quotients. Multiples of its square have zero weight.
open Classical in
private theorem sum_moebius {f : F[X]} (hf : f.Monic) :
    ∑ g ∈ divisors f, (moebius g : ℂ) = if f = 1 then 1 else 0 := by
  by_cases h : f = 1
  · subst f
    have he : divisors (1 : F[X]) = {1} := by
      ext g
      simp only [mem_divisors one_ne_zero, Finset.mem_singleton]
      exact ⟨fun hg => hg.1.isUnit_iff.mp (isUnit_of_dvd_one hg.2),
        by rintro rfl; exact ⟨monic_one, dvd_rfl⟩⟩
    simp [he]
  · obtain ⟨p, hp, hirr, hd⟩ := exists_monic_irreducible_factor f (hf.isUnit_iff.not.mpr h)
    rw [ite_eq_right h, ← Finset.sum_filter_add_sum_filter_not _ (p ∣ ·)]
    have hmul : ∑ g ∈ (divisors f).filter (p ∣ ·), (moebius g : ℂ) =
        ∑ g ∈ divisors (f /ₘ p), (moebius (p * g) : ℂ) := by
      symm
      refine (sum_divisors_mul hp hf hd (fun g => (moebius (p * g) : ℂ))).trans ?_
      exact Finset.sum_congr rfl fun g hg => by rw [mul_quotient hp (Finset.mem_filter.mp hg).2]
    rw [hmul, ← Finset.sum_filter_of_ne (p := fun g => ¬ p ∣ g)]
    · have he : (divisors (f /ₘ p)).filter (fun g => ¬ p ∣ g) =
          (divisors f).filter (fun g => ¬ p ∣ g) := by
        ext g
        simp only [Finset.mem_filter, mem_divisors hf.ne_zero,
          mem_divisors (monic_quotient hp hf hd).ne_zero]
        constructor
        · rintro ⟨⟨hm, hdiv⟩, hn⟩
          exact ⟨⟨hm, hdiv.trans ⟨p, by rw [mul_comm, mul_quotient hp hd]⟩⟩, hn⟩
        · rintro ⟨⟨hm, hdiv⟩, hn⟩
          have hh := (hirr.isRelPrime_iff_not_dvd.mpr hn).mul_dvd hd hdiv
          exact ⟨⟨hm, (mul_dvd_mul_iff_left hp.ne_zero).mp
            (by rwa [mul_quotient hp hd])⟩, hn⟩
      rw [he, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro g hg
      rw [(hirr.isRelPrime_iff_not_dvd.mpr (Finset.mem_filter.mp hg).2).moebius_mul,
        hirr.moebius_eq]
      simp
    · intro g _ hμ hpg
      have hs : ¬ Squarefree (p * g) :=
        fun hsf => hirr.not_isUnit (hsf p (mul_dvd_mul_left p hpg))
      exact hμ (by simp [moebius_of_not_squarefree hs])

private theorem sum_conv_moebius (γ : F[X] → ℂ) {f : F[X]} (hf : f.Monic) :
    ∑ g ∈ divisors f, monicDirichletConv γ (fun r => (moebius r : ℂ)) g = γ f := by
  classical
  let s := divisors f
  have hinner (g : F[X]) (hg : g ∈ s) :
      monicDirichletConv γ (fun r => (moebius r : ℂ)) g =
        ∑ a ∈ s.filter (· ∣ g), γ a * (moebius (g /ₘ a) : ℂ) := by
    obtain ⟨hm, hd⟩ := (mem_divisors hf.ne_zero).mp hg
    rw [conv_eq_sum _ _ hm]
    congr 1
    ext a
    simp only [Finset.mem_filter, s, mem_divisors hf.ne_zero, mem_divisors hm.ne_zero]
    exact ⟨fun h => ⟨⟨h.1, h.2.trans hd⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  change ∑ g ∈ s, _ = _
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm' (t' := s) (s' := fun a => s.filter (a ∣ ·))]
  · rw [Finset.sum_eq_single f]
    · simp only [← Finset.mul_sum]
      rw [← sum_divisors_mul hf hf dvd_rfl (fun r => (moebius r : ℂ)),
        sum_moebius (monic_quotient hf hf dvd_rfl)]
      have hq : f /ₘ f = 1 := by
        simpa using mul_divByMonic_cancel_left (1 : F[X]) hf
      simp [hq]
    · intro a ha haf
      have ⟨hm, hd⟩ := (mem_divisors hf.ne_zero).mp ha
      have hn : f /ₘ a ≠ 1 := fun h => haf (by simpa [h] using mul_quotient hm hd)
      rw [← Finset.mul_sum, ← sum_divisors_mul hm hf hd (fun r => (moebius r : ℂ)),
        sum_moebius (monic_quotient hm hf hd), ite_eq_right hn, mul_zero]
    · exact fun h => (h ((mem_divisors hf.ne_zero).mpr ⟨hf, dvd_rfl⟩)).elim
  · intro g a
    simp only [Finset.mem_filter]
    tauto

private noncomputable def pairs [Finite F] (k : ℤ) : Finset (F[X] × F[X]) :=
  (monics k ×ˢ monics k).filter
    (fun p => (p.1.natDegree : ℤ) + p.2.natDegree ≤ k)

private theorem mem_pairs [Finite F] {k : ℤ} {p : F[X] × F[X]} :
    p ∈ pairs k ↔ p.1.Monic ∧ p.2.Monic ∧ (p.1.natDegree : ℤ) + p.2.natDegree ≤ k := by
  rcases p with ⟨a, b⟩
  simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_monics]
  constructor
  · rintro ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, h⟩
    exact ⟨h₁, h₂, h⟩
  · rintro ⟨h₁, h₂, h⟩
    exact ⟨⟨⟨h₁, by omega⟩, ⟨h₂, by omega⟩⟩, h⟩

-- The pair (g, f /ₘ g) records a monic factorization of f.
private theorem sum_conv_eq_pairs [Finite F] (α β w : F[X] → ℂ) (k : ℤ) :
    ∑ f ∈ monics k, w f * monicDirichletConv α β f =
      ∑ p ∈ pairs k, w (p.1 * p.2) * (α p.1 * β p.2) := by
  calc
    _ = ∑ f ∈ monics k, ∑ g ∈ divisors f, w f * (α g * β (f /ₘ g)) := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [conv_eq_sum _ _ (mem_monics.mp hf).1, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_sigma']
      apply Finset.sum_bij (fun p _ => (p.2, p.1 /ₘ p.2))
      · intro p hp
        obtain ⟨hf, hk⟩ := mem_monics.mp (Finset.mem_sigma.mp hp).1
        obtain ⟨hg, hd⟩ := (mem_divisors hf.ne_zero).mp (Finset.mem_sigma.mp hp).2
        have hq := monic_quotient hg hf hd
        have he := natDegree_mul hg.ne_zero hq.ne_zero
        rw [mul_quotient hg hd] at he
        exact mem_pairs.mpr ⟨hg, hq, by dsimp; omega⟩
      · intro p hp q hq h
        have he := congrArg Prod.fst h
        have hprod := congrArg (fun t : F[X] × F[X] => t.1 * t.2) h
        have hp' := (mem_divisors (mem_monics.mp (Finset.mem_sigma.mp hp).1).1.ne_zero).mp
          (Finset.mem_sigma.mp hp).2
        have hq' := (mem_divisors (mem_monics.mp (Finset.mem_sigma.mp hq).1).1.ne_zero).mp
          (Finset.mem_sigma.mp hq).2
        dsimp at he hprod
        rw [mul_quotient hp'.1 hp'.2, mul_quotient hq'.1 hq'.2] at hprod
        exact Sigma.ext hprod (heq_of_eq he)
      · rintro ⟨a, b⟩ hp
        obtain ⟨ha, hb, hk⟩ := mem_pairs.mp hp
        refine ⟨⟨a * b, a⟩, Finset.mem_sigma.mpr
          ⟨mem_monics.mpr ⟨ha.mul hb, ?_⟩,
            (mem_divisors (ha.mul hb).ne_zero).mpr ⟨ha, dvd_mul_right a b⟩⟩, ?_⟩
        · rw [natDegree_mul ha.ne_zero hb.ne_zero]
          omega
        · simp [mul_divByMonic_cancel_left b ha]
      · intro p hp
        have h := (mem_divisors (mem_monics.mp (Finset.mem_sigma.mp hp).1).1.ne_zero).mp
          (Finset.mem_sigma.mp hp).2
        dsimp
        rw [mul_quotient h.1 h.2]

open Classical in
private theorem sum_pairs_mul [Finite F] (α β : F[X] →* ℂ) (k : ℤ) {d e : F[X]}
    (hd : d.Monic) (he : e.Monic) :
    (α d * β e) * (∑ p ∈ pairs (k - (d * e).natDegree), α p.1 * β p.2) =
      ∑ p ∈ (pairs k).filter (fun p => d ∣ p.1 ∧ e ∣ p.2), α p.1 * β p.2 := by
  rw [Finset.mul_sum]
  have hdeg := natDegree_mul hd.ne_zero he.ne_zero
  apply Finset.sum_bij (fun p _ => (d * p.1, e * p.2))
  · intro p hp
    obtain ⟨ha, hb, hk⟩ := mem_pairs.mp hp
    refine Finset.mem_filter.mpr ⟨mem_pairs.mpr ⟨hd.mul ha, he.mul hb, ?_⟩,
      dvd_mul_right _ _, dvd_mul_right _ _⟩
    dsimp
    rw [natDegree_mul hd.ne_zero ha.ne_zero, natDegree_mul he.ne_zero hb.ne_zero]
    omega
  · intro p _ q _ h
    exact Prod.ext (mul_left_cancel₀ hd.ne_zero (congrArg Prod.fst h))
      (mul_left_cancel₀ he.ne_zero (congrArg Prod.snd h))
  · intro p hp
    obtain ⟨hp, hda, heb⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb, hk⟩ := mem_pairs.mp hp
    have haq := monic_quotient hd ha hda
    have hbq := monic_quotient he hb heb
    have ha' := mul_quotient hd hda
    have hb' := mul_quotient he heb
    have hdeg₁ := natDegree_mul hd.ne_zero haq.ne_zero
    have hdeg₂ := natDegree_mul he.ne_zero hbq.ne_zero
    rw [ha'] at hdeg₁
    rw [hb'] at hdeg₂
    exact ⟨(p.1 /ₘ d, p.2 /ₘ e), mem_pairs.mpr ⟨haq, hbq, by dsimp; omega⟩,
      Prod.ext ha' hb'⟩
  · intro p _
    dsimp
    rw [map_mul, map_mul]
    ac_rfl

-- For a factorization a * b, Möbius cancellation selects d = f / gcd(f, b).
open Classical in
private theorem divisor_coefficient {f a b : F[X]} (hf : f.Monic) :
    (∑ d ∈ divisors f, ∑ ℓ ∈ divisors d,
      if d ∣ a ∧ (f /ₘ d) * ℓ ∣ b then (moebius ℓ : ℂ) else 0) =
        if f ∣ a * b then 1 else 0 := by
  let : StrongNormalizedGCDMonoid F[X] := toStrongNormalizedGCDMonoid _
  let t := gcd f b
  have ht : t.Monic :=
    (normalize_eq_self_iff_monic (gcd_ne_zero_of_left hf.ne_zero)).mp
      (StrongNormalizedGCDMonoid.normalize_gcd f b)
  let d₀ := f /ₘ t
  have hd₀ := monic_quotient ht hf (gcd_dvd_left f b)
  have ht₀ : t * d₀ = f := mul_quotient ht (gcd_dvd_left f b)
  have hd₀f : d₀ ∣ f := ⟨t, by rw [mul_comm, ht₀]⟩
  have hd₀a : d₀ ∣ a ↔ f ∣ a * b := by
    rw [mul_comm a b, ← dvd_gcd_mul_iff_dvd_mul]
    change d₀ ∣ a ↔ f ∣ t * a
    rw [← ht₀, mul_dvd_mul_iff_left ht.ne_zero]
  rw [← hd₀a]
  calc
    _ = ∑ d ∈ divisors f, if d = d₀ ∧ d₀ ∣ a then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hdmem
      obtain ⟨hd, hdf⟩ := (mem_divisors hf.ne_zero).mp hdmem
      let e := f /ₘ d
      have he : e.Monic := monic_quotient hd hf hdf
      have hfe : e * d = f := (mul_comm _ _).trans (mul_quotient hd hdf)
      have htd : t = e ↔ d = d₀ := by
        constructor
        · intro h
          apply mul_left_cancel₀ ht.ne_zero
          rw [ht₀, h, hfe]
        · intro h
          apply mul_right_cancel₀ hd₀.ne_zero
          exact ht₀.trans (hfe.symm.trans (congrArg (e * ·) h))
      change (∑ ℓ ∈ divisors d, if d ∣ a ∧ e * ℓ ∣ b then (moebius ℓ : ℂ) else 0) = _
      by_cases hda : d ∣ a
      · simp only [hda, true_and, ← Finset.sum_filter]
        by_cases heb : e ∣ b
        · let x := b /ₘ e
          let s := gcd d x
          have hbx : e * x = b := mul_quotient he heb
          have hs : s.Monic :=
            (normalize_eq_self_iff_monic (gcd_ne_zero_of_left hd.ne_zero)).mp
              (StrongNormalizedGCDMonoid.normalize_gcd d x)
          have hts : e * s = t := by
            calc
              e * s = gcd (e * d) (e * x) := by
                rw [gcd_mul_left, he.normalize_eq_self, mul_comm]
              _ = t := by rw [hfe, hbx]
          have hs₁ : s = 1 ↔ t = e :=
            ⟨fun h => by rw [← hts, h, mul_one], fun h =>
              mul_left_cancel₀ he.ne_zero (by rw [hts, h, mul_one])⟩
          have hfilter : (divisors d).filter (fun ℓ => e * ℓ ∣ b) = divisors s := by
            ext ℓ
            simp only [Finset.mem_filter, mem_divisors hd.ne_zero, mem_divisors hs.ne_zero]
            have hl : e * ℓ ∣ b ↔ ℓ ∣ x := by
              rw [← hbx, mul_dvd_mul_iff_left he.ne_zero]
            rw [hl, dvd_gcd_iff]
            exact and_assoc
          rw [hfilter, sum_moebius hs]
          simp only [hs₁, htd]
          by_cases h : d = d₀
          · have ha : d₀ ∣ a := h ▸ hda
            simp [h, ha]
          · simp [h]
        · have hn : ¬ d = d₀ := fun h => heb ((htd.mpr h) ▸ gcd_dvd_right f b)
          rw [ite_eq_right (fun h => hn h.1)]
          exact Finset.sum_eq_zero fun ℓ h =>
            (heb ((dvd_mul_right e ℓ).trans (Finset.mem_filter.mp h).2)).elim
      · have hn : ¬ (d = d₀ ∧ d₀ ∣ a) := fun ⟨h, h'⟩ => hda (h.symm ▸ h')
        simp [hda, hn]
    _ = _ := by
      by_cases h : d₀ ∣ a
      · have hm : d₀ ∈ divisors f := (mem_divisors hf.ne_zero).mpr ⟨hd₀, hd₀f⟩
        simp [h, hm]
      · simp [h]

private theorem partial_eq_pairs [Finite F] (α β : F[X] → ℂ) (k : ℤ) :
    monicConvPartialSum α β k = ∑ p ∈ pairs k, α p.1 * β p.2 := by
  rw [monicConvPartialSum, finsum_mem_eq_finite_toFinset_sum _ (finite_monics k)]
  simpa only [monics, one_mul] using sum_conv_eq_pairs α β (fun _ => 1) k

open Classical in
private theorem divisor_sum_eq_pairs [Finite F] (α β : F[X] →* ℂ) {f : F[X]}
    (hf : f.Monic) (k : ℤ) :
    (∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
      ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
        (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β (k - (f * ℓ).natDegree)) =
      ∑ p ∈ (pairs k).filter (fun p => f ∣ p.1 * p.2), α p.1 * β p.2 := by
  let w (p : F[X] × F[X]) := α p.1 * β p.2
  rw [finsum_divisors hf.ne_zero]
  calc
    _ = ∑ d ∈ divisors f, ∑ ℓ ∈ divisors d, (moebius ℓ : ℂ) *
          ∑ p ∈ (pairs k).filter (fun p => d ∣ p.1 ∧ (f /ₘ d) * ℓ ∣ p.2), w p := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdm, hdf⟩ := (mem_divisors hf.ne_zero).mp hd
      rw [finsum_divisors hdm.ne_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hℓm := ((mem_divisors hdm.ne_zero).mp hℓ).1
      have hprod : d * ((f /ₘ d) * ℓ) = f * ℓ := by
        rw [← mul_assoc, mul_quotient hdm hdf]
      dsimp only [w]
      rw [partial_eq_pairs, ← hprod, ← sum_pairs_mul α β k hdm
        ((monic_quotient hdm hf hdf).mul hℓm), map_mul]
      ac_rfl
    _ = ∑ d ∈ divisors f, ∑ ℓ ∈ divisors d, ∑ p ∈ pairs k,
          (if d ∣ p.1 ∧ (f /ₘ d) * ℓ ∣ p.2 then (moebius ℓ : ℂ) else 0) * w p := by
      simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
    _ = ∑ p ∈ pairs k, (∑ d ∈ divisors f, ∑ ℓ ∈ divisors d,
          if d ∣ p.1 ∧ (f /ₘ d) * ℓ ∣ p.2 then (moebius ℓ : ℂ) else 0) * w p := by
      simp_rw [Finset.sum_mul]
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      rw [divisor_coefficient hf]
      split <;> simp [w]

-- Expand the weight by Möbius inversion, then sum in the opposite order.
open Classical in
private theorem sum_weighted_pairs [Finite F] (γ α β : F[X] → ℂ) (k : ℤ) :
    (∑ p ∈ pairs k, γ (p.1 * p.2) * (α p.1 * β p.2)) =
      ∑ f ∈ monics k, monicDirichletConv γ (fun g => (moebius g : ℂ)) f *
        ∑ p ∈ (pairs k).filter (fun p => f ∣ p.1 * p.2), α p.1 * β p.2 := by
  let c := monicDirichletConv γ (fun g => (moebius g : ℂ))
  let w (p : F[X] × F[X]) := α p.1 * β p.2
  calc
    _ = ∑ p ∈ pairs k, ∑ f ∈ (monics k).filter (· ∣ p.1 * p.2), c f * w p := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨ha, hb, hk⟩ := mem_pairs.mp hp
      have he : (monics k).filter (· ∣ p.1 * p.2) = divisors (p.1 * p.2) := by
        ext f
        rw [Finset.mem_filter, mem_monics, mem_divisors (ha.mul hb).ne_zero]
        constructor
        · rintro ⟨⟨hm, _⟩, hd⟩
          exact ⟨hm, hd⟩
        · rintro ⟨hm, hd⟩
          have hle := natDegree_le_of_dvd hd (ha.mul hb).ne_zero
          rw [natDegree_mul ha.ne_zero hb.ne_zero] at hle
          exact ⟨⟨hm, by omega⟩, hd⟩
      rw [he, ← Finset.sum_mul, sum_conv_moebius γ (ha.mul hb)]
    _ = _ := by
      rw [Finset.sum_comm' (t' := monics k)
        (s' := fun f => (pairs k).filter (fun p => f ∣ p.1 * p.2))]
      · simp only [Finset.mul_sum, c, w]
      · intro p f
        simp only [Finset.mem_filter]
        tauto

end weightedMonicConvSum_eq_of_completelyMultiplicative

open weightedMonicConvSum_eq_of_completelyMultiplicative in
/-- **Camargo's identity over $F[T]$.** Let $F$ be a finite field and let $\mu$ be the Möbius
function of $F[T]$. For functions $\alpha, \beta \colon F[T] \to \mathbb{C}$ let
$(\alpha * \beta)(f) = \sum_{g \mid f} \alpha(g) \beta(f/g)$, over monic divisors $g$, be their
Dirichlet convolution, and let $D[\alpha, \beta](k)$ be the sum of $(\alpha * \beta)(g)$ over the
monic $g$ of degree at most $k$, which is $0$ for $k < 0$. For a further function $\gamma$ let
$D[\gamma, \alpha, \beta](n)$ be the sum of $\gamma(f) (\alpha * \beta)(f)$ over the monic $f$ of
degree at most $n$. Suppose $\alpha$ and $\beta$ are completely multiplicative, that is,
$\alpha(1) = 1$ and $\alpha(f g) = \alpha(f) \alpha(g)$ for all $f, g \in F[T]$, and likewise for
$\beta$, and let $\gamma \colon F[T] \to \mathbb{C}$ be arbitrary. Then for every natural number
$n$,

$$D[\gamma, \alpha, \beta](n) = \sum_{f \text{ monic},\ \deg f \le n} (\gamma * \mu)(f)
\sum_{d \mid f} \alpha(d) \beta(f/d) \sum_{\ell \mid d} \mu(\ell) \beta(\ell) \,
D[\alpha, \beta](n - \deg(f \ell)),$$

where $d$ runs over the monic divisors of $f$ and $\ell$ over the monic divisors of $d$.

Source: Habib Jaber and Matilde Lalín, *Dirichlet Convolutions and Divisor Problems over B-Free
Polynomials over Function Fields*, INTEGERS 26 (2026), Article A80, Theorem 6
(`integers-2026-A80-thm-6`). -/
public theorem weightedMonicConvSum_eq_of_completelyMultiplicative {F : Type*} [Field F]
    [Finite F] (γ : F[X] → ℂ) (α β : F[X] →* ℂ) (n : ℕ) :
    weightedMonicConvSum γ α β n =
      ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ f.natDegree ≤ n},
        monicDirichletConv γ (fun g => (moebius g : ℂ)) f *
          ∑ᶠ d ∈ {d : F[X] | d.Monic ∧ d ∣ f}, α d * β (f /ₘ d) *
            ∑ᶠ ℓ ∈ {ℓ : F[X] | ℓ.Monic ∧ ℓ ∣ d},
              (moebius ℓ : ℂ) * β ℓ * monicConvPartialSum α β ((n : ℤ) - (f * ℓ).natDegree) := by
  classical
  have hset : {f : F[X] | f.Monic ∧ f.natDegree ≤ n} =
      {f : F[X] | f.Monic ∧ (f.natDegree : ℤ) ≤ (n : ℤ)} := by
    ext f
    simp
  rw [weightedMonicConvSum, hset]
  simp only [finsum_mem_eq_finite_toFinset_sum _ (finite_monics (F := F) (n : ℤ))]
  change (∑ f ∈ monics (n : ℤ), _) = ∑ f ∈ monics (n : ℤ), _
  rw [sum_conv_eq_pairs, sum_weighted_pairs]
  apply Finset.sum_congr rfl
  intro f hf
  rw [divisor_sum_eq_pairs α β (mem_monics.mp hf).1]

end MetaMathlibExt
