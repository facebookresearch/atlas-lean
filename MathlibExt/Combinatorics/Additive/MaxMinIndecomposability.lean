/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Max-min coefficient products and lunar primes

The coefficient formulas use sequences of natural numbers, with max-min convolution
as multiplication. A lunar prime candidate has a nonzero constant term and its
largest digit occurs somewhere; these conditions force a monomial factor to be
the lunar unit.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Max-min product.** The max-min product of sequences $g, h \colon \mathbb{N} \to \mathbb{N}$
is the sequence $g \otimes h$ with $(g \otimes h)_k = \max_{i + j = k} \min(g_i, h_j)$ for every
$k \in \mathbb{N}$, the maximum running over pairs of natural numbers $(i, j)$. This is the product
of the max-min semiring $(\mathbb{N}, \max, \min)$ on coefficient sequences.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public def maxMinMul (g h : ℕ → ℕ) : ℕ → ℕ :=
  fun k => (Finset.antidiagonal k).sup fun p => min (g p.1) (h p.2)

/-- **Constant coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_0 = \min(g_0, h_0)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_zero (g h : ℕ → ℕ) : maxMinMul g h 0 = min (g 0) (h 0) := by
  simp [maxMinMul]

/-- **Linear coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_1 = \max(\min(g_0, h_1), \min(g_1, h_0))$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_one (g h : ℕ → ℕ) :
    maxMinMul g h 1 = max (min (g 0) (h 1)) (min (g 1) (h 0)) := by
  simp [maxMinMul, Finset.Nat.antidiagonal_succ]

/-- **Monomials over the max-min semiring.** A coefficient sequence
$g : \mathbb{N} \to \mathbb{N}$ over the max-min semiring is a monomial when exactly one of its
entries is nonzero, that is, when it is $c x^i$ for some index $i$ and some coefficient $c \neq 0$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public def IsMaxMinMonomial (g : ℕ → ℕ) : Prop :=
  ∃ i, ∀ j, g j ≠ 0 ↔ j = i

/-- **The zero sequence is not a monomial.** The zero coefficient sequence
$\mathbb{N} \to \mathbb{N}$ is not a max-min monomial: a monomial has exactly one nonzero
entry, and the zero sequence has none.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinMonomial_zero : ¬ IsMaxMinMonomial 0 := by
  rintro ⟨i, hi⟩
  exact (hi i).2 rfl rfl

/-- **Max-min indecomposable sequences.** The predicate `IsMaxMinIndecomposable` records the
factorization condition: for all sequences $g, h : \mathbb{N} \to \mathbb{N}$ with
$g \otimes h = f$, where $\otimes$ is the max-min product, $g$ or $h$ is a monomial, that is,
a sequence with exactly one nonzero term. The paper's Definition 5 additionally excludes
monomials; this predicate does not include that exclusion.

Factors here are arbitrary natural-valued sequences, and a monomial has exactly one nonzero
coefficient. Definition 5 uses finite base-$b$ polynomials and writes monomials as $t x^n$,
allowing $t = 0$. For a digit sequence with nonzero constant term, any factorization has
nonzero, finitely supported factors: a nonzero coefficient of either factor survives by pairing
with the other factor's nonzero constant term. For $b \ge 2$, clipping the factors at $b - 1$
preserves their supports, the max-min product clipped at $b - 1$, and thus the monomial condition.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 5. -/
public def IsMaxMinIndecomposable (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, maxMinMul g h = f → IsMaxMinMonomial g ∨ IsMaxMinMonomial h

/-- **The zero sequence is decomposable.** The zero coefficient sequence
$\mathbb{N} \to \mathbb{N}$ is not indecomposable over the max-min semiring: it factors as
$0 = 0 \otimes 0$, where $\otimes$ is the max-min product, and the zero sequence is not a
monomial.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinIndecomposable_zero : ¬ IsMaxMinIndecomposable 0 := by
  intro h
  have h0 : maxMinMul (0 : ℕ → ℕ) 0 = 0 := by
    funext k
    simp [maxMinMul]
  rcases h 0 0 h0 with h1 | h1 <;> exact not_isMaxMinMonomial_zero h1

/-- **Coefficient sequence of a digit string.** Let $n$ and $b$ be natural numbers. The
coefficient sequence of a digit string $a = (a_0, \dots, a_{n-1})$ with digits in
$\{0, \dots, b - 1\}$ is the sequence $\mathbb{N} \to \mathbb{N}$ whose $k$-th term is $a_k$ for
$k < n$ and $0$ for $k \ge n$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public def digitSeq {n b : ℕ} (a : Fin n → Fin b) : ℕ → ℕ :=
  fun k => if hk : k < n then (a ⟨k, hk⟩ : ℕ) else 0

/-- **A digit string has no coefficients beyond its length.** Let $n$ and $b$ be natural numbers
and let $a = (a_0, \dots, a_{n-1})$ be a digit string with digits in $\{0, \dots, b - 1\}$. Then
for every $k \ge n$, the $k$-th term of the coefficient sequence of $a$ is $0$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public theorem digitSeq_of_le {n b : ℕ} (a : Fin n → Fin b) {k : ℕ} (hk : n ≤ k) :
    digitSeq a k = 0 := by
  simp [digitSeq, Nat.not_lt.2 hk]

/-- **Lunar unit.** For a natural number $b$, the lunar unit of base $b$ is the coefficient sequence
$\mathbb{N} \to \mathbb{N}$ whose constant term is $b - 1$ and whose other terms are all $0$, that
is, the constant polynomial $b - 1$ over the max-min semiring. The subtraction is truncated, so
the lunar unit of base $0$ is the zero sequence.

For sequences with all terms less than $b$, the lunar unit is the identity of the max-min product.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public def lunarUnit (b : ℕ) : ℕ → ℕ :=
  fun k => if k = 0 then b - 1 else 0

/-- **The lunar unit is a monomial.** For every natural number $b \ge 2$, the lunar unit of base
$b$, the sequence with constant term $b - 1$ and all other terms $0$, is a max-min monomial: it
has exactly one nonzero term.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public theorem isMaxMinMonomial_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsMaxMinMonomial (lunarUnit b) :=
  ⟨0, fun j => by by_cases hj : j = 0 <;> simp [lunarUnit, hj]; omega⟩

/-- **Lunar primes.** Let $b$ be a natural number. The lunar unit of base $b$ is the constant
polynomial $b - 1$. The predicate `IsLunarPrime` records the factorization condition: for
all sequences $g, h : \mathbb{N} \to \mathbb{N}$ with all terms less than $b$ and
$g \otimes h = f$, at least one factor is the lunar unit. The paper's Definition 5 additionally
requires $f$ to be a nonunit; this predicate does not include that exclusion. Moreover,
Definition 5 restricts $f$ and the factors to finite base-$b$ polynomials. Here $f$ is
unrestricted: the predicate can hold vacuously if $f$ has no factorization by base-$b$
sequences. For a digit sequence with nonzero constant term, every factorization has finite
support in both factors, since pairing each nonzero coefficient with the other factor's
nonzero constant term gives a nonzero product coefficient.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 5. -/
public def IsLunarPrime (b : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, (∀ i, g i < b) → (∀ i, h i < b) → maxMinMul g h = f →
    g = lunarUnit b ∨ h = lunarUnit b

/-- **Zero is not a lunar prime.** For every integer $b \ge 2$, the zero sequence is not a lunar
prime of base $b$: $0 = 0 \otimes 0$, where $\otimes$ is the max-min product, and $0$ is not the
lunar unit, the constant polynomial $b - 1$ with coefficient sequence $(b - 1, 0, 0, \dots)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public theorem not_isLunarPrime_zero {b : ℕ} (hb : 2 ≤ b) : ¬ IsLunarPrime b 0 := by
  intro h
  have h0 : maxMinMul (0 : ℕ → ℕ) 0 = 0 := by
    funext k
    simp [maxMinMul]
  have hne : (0 : ℕ → ℕ) ≠ lunarUnit b := by
    intro he
    have := congrFun he 0
    simp [lunarUnit] at this
    omega
  rcases h 0 0 (fun _ => by simp; omega) (fun _ => by simp; omega) h0 with h1 | h1 <;>
    exact hne h1

/-- **Lunar prime candidates.** Let $b$ be a natural number. A coefficient sequence
$f : \mathbb{N} \to \mathbb{N}$ is a prime candidate in base $b$ when its constant term $f_0$ is
nonzero and some term $f_i$ equals $b - 1$, where the subtraction is truncated, so that
$b - 1 = 0$ when $b = 0$. For $f$ with all terms less than $b$, the second condition says that
the largest coefficient of $f$ is $b - 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public def IsLunarPrimeCandidate (b : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 ≠ 0 ∧ ∃ i, f i = b - 1

/-- **The lunar unit is a prime candidate.** For every natural number $b \ge 2$, the lunar unit
of base $b$, the sequence with constant term $b - 1$ and all other terms $0$, is a prime candidate
in base $b$: its constant term is nonzero and one of its terms equals $b - 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public theorem isLunarPrimeCandidate_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsLunarPrimeCandidate b (lunarUnit b) :=
  ⟨by simp [lunarUnit]; omega, 0, by simp [lunarUnit]⟩

/- The factorization part of Lemma 30, preserving the legacy statement. The full
source statement, including the exclusions in Definition 5, is proved below. -/
public theorem isLunarPrime_of_indecomposable_candidate {n b : ℕ} (hb : 2 ≤ b)
    (a : Fin n → Fin b) (hc : IsLunarPrimeCandidate b (digitSeq a))
    (hi : IsMaxMinIndecomposable (digitSeq a)) :
    IsLunarPrime b (digitSeq a) := by
  intro g h hg hh hprod
  have hconst : min (g 0) (h 0) ≠ 0 := by
    rw [← maxMinMul_zero, hprod]
    exact hc.1
  have hg₀ : g 0 ≠ 0 := fun hz => hconst (by simp [hz])
  have hh₀ : h 0 ≠ 0 := fun hz => hconst (by simp [hz])
  obtain ⟨k, hk⟩ := hc.2
  have hne : (Finset.antidiagonal k).Nonempty :=
    ⟨(0, k), Finset.mem_antidiagonal.mpr (zero_add k)⟩
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.antidiagonal k) hne
    (fun p => min (g p.1) (h p.2))
  have htop : maxMinMul g h k = b - 1 := (congrFun hprod k).trans hk
  have hmin : min (g p.1) (h p.2) = b - 1 := hp.symm.trans htop
  have hgp : g p.1 = b - 1 := by
    have hle := min_le_left (g p.1) (h p.2)
    have hlt := hg p.1
    omega
  have hhp : h p.2 = b - 1 := by
    have hle := min_le_right (g p.1) (h p.2)
    have hlt := hh p.2
    omega
  -- A monomial with nonzero constant term is supported only at zero. If it also
  -- attains the largest digit, that digit is its constant term.
  have unit_of_monomial {s : ℕ → ℕ} (hs : IsMaxMinMonomial s) (hs₀ : s 0 ≠ 0)
      (i : ℕ) (hmax : s i = b - 1) : s = lunarUnit b := by
    obtain ⟨j, hj⟩ := hs
    have hj₀ : j = 0 := ((hj 0).1 hs₀).symm
    have hi₀ : i = 0 := ((hj i).1 (by omega)).trans hj₀
    subst i
    funext t
    by_cases ht : t = 0
    · subst t
      simpa [lunarUnit] using hmax
    · have hz : s t = 0 := by
        by_contra hne
        exact ht (((hj t).1 hne).trans hj₀)
      simp [lunarUnit, ht, hz]
  rcases hi g h hprod with hm | hm
  · exact Or.inl (unit_of_monomial hm hg₀ p.1 hgp)
  · exact Or.inr (unit_of_monomial hm hh₀ p.2 hhp)

/-- **Indecomposable prime candidates are lunar primes.** Let $b \ge 2$, and let $f$ be the
coefficient sequence of a base-$b$ digit string. Suppose $f$ is a prime candidate, is not a
monomial, and every max-min factorization of $f$ has a monomial factor. Then $f$ differs from
the lunar unit and every factorization by base-$b$ coefficient sequences has a unit factor.

The nonmonomial hypothesis and nonunit conclusion are the exclusions from Definition 5.
The predicates `IsMaxMinIndecomposable` and `IsLunarPrime` record just the factorization
conditions, so the exclusions are stated explicitly here.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 30
(`jis-2025-25.2.7-lem-30`), attributed to Applegate, LeBrun and Sloane. -/
public theorem isLunarPrime_of_nonmonomial_indecomposable_candidate {n b : ℕ} (hb : 2 ≤ b)
    (a : Fin n → Fin b) (hc : IsLunarPrimeCandidate b (digitSeq a))
    (hnot : ¬ IsMaxMinMonomial (digitSeq a)) (hi : IsMaxMinIndecomposable (digitSeq a)) :
    digitSeq a ≠ lunarUnit b ∧ IsLunarPrime b (digitSeq a) := by
  refine ⟨?_, isLunarPrime_of_indecomposable_candidate hb a hc hi⟩
  intro he
  exact hnot (he.symm ▸ isMaxMinMonomial_lunarUnit hb)

end

end MetaMathlibExt
