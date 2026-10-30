/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indecomposability over the max-min semiring

Statements from Benjamin Baily, Justine Dell, Henry L. Fleischmann, Faye Jackson, Ethan Pesikoff,
Steven J. Miller and Luke Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of
Integer Sequences 28 (2025), Article 25.2.7.

A polynomial or power series over the max-min semiring `(ℕ, max, min)` is recorded by its
coefficient sequence `ℕ → ℕ`. Addition is the pointwise maximum (`⊔` on functions) and the product
is the max-min convolution `(g ⊗ h)ₖ = max_{i + j = k} min(gᵢ, hⱼ)`. Lunar numbers in base `b`
are the polynomials with coefficients in `{0, …, b - 1}`; a lunar number with `n` digits is a
digit string `a : Fin n → Fin b` whose leading digit `a (n - 1)` is nonzero (degree `n - 1`).
Boolean polynomials are recorded by their supports `A ⊆ ℕ`: the product of two Boolean
polynomials has support the sumset `A + B`, and `|f|` is `A.card`.

The definitions follow the arXiv version of the paper (arXiv:2111.09786, titled *Irreducibility
Over the Max-Min Semiring*), where the JIS "indecomposable" is called "irreducible" and the JIS
`ℒ_b^n` is the set of degree-`n` polynomials of `ℬ_b[x]`. The quantitative statements of
Section 2 (Proposition 21 to Lemma 28) follow the JIS text, where `ℒ_b^n` is the set of lunar
numbers of degree at most `n`, recorded by digit strings `Fin (n + 1) → Fin b`. Proposition 20
(Hoeffding's inequality) is the proved `ProbabilityTheory.hoeffding_bernoulli_sum_abs_tail`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace MetaMathlibExt

@[expose] public section

open Pointwise Filter Topology

/-- The max-min convolution `(g ⊗ h)ₖ = max_{i + j = k} min(gᵢ, hⱼ)`, the product of the
max-min semiring `(ℕ, max, min)` on coefficient sequences.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public def maxMinMul (g h : ℕ → ℕ) : ℕ → ℕ :=
  fun k => (Finset.antidiagonal k).sup fun p => min (g p.1) (h p.2)

/-- The constant coefficient of a max-min product: `(g ⊗ h)₀ = min(g₀, h₀)`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_zero (g h : ℕ → ℕ) : maxMinMul g h 0 = min (g 0) (h 0) := by
  simp [maxMinMul]

/-- The linear coefficient of a max-min product: `(g ⊗ h)₁ = max(min(g₀, h₁), min(g₁, h₀))`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_one (g h : ℕ → ℕ) :
    maxMinMul g h 1 = max (min (g 0) (h 1)) (min (g 1) (h 0)) := by
  simp [maxMinMul, Finset.Nat.antidiagonal_succ]

/-- A max-min monomial `c xⁱ` with `c ≠ 0`: a coefficient sequence with exactly one nonzero
entry.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public def IsMaxMinMonomial (g : ℕ → ℕ) : Prop :=
  ∃ i, ∀ j, g j ≠ 0 ↔ j = i

/-- The zero sequence is not a monomial.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinMonomial_zero : ¬ IsMaxMinMonomial 0 := by
  rintro ⟨i, hi⟩
  exact (hi i).2 rfl rfl

/-- An indecomposable (in the arXiv version: irreducible) element: `f = g ⊗ h` forces `g` or `h`
to be a monomial. Factors range over all sequences `ℕ → ℕ`; for `f` with coefficients below `b`
this is equivalent to factoring over `ℬ_b`, by applying the digit map `min (·) (b - 1)`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public def IsMaxMinIndecomposable (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, maxMinMul g h = f → IsMaxMinMonomial g ∨ IsMaxMinMonomial h

/-- The zero sequence is decomposable: `0 = 0 ⊗ 0`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinIndecomposable_zero : ¬ IsMaxMinIndecomposable 0 := by
  intro h
  have h0 : maxMinMul (0 : ℕ → ℕ) 0 = 0 := by
    funext k
    simp [maxMinMul]
  rcases h 0 0 h0 with h1 | h1 <;> exact not_isMaxMinMonomial_zero h1

/-- The coefficient sequence of the digit string `a : Fin n → Fin b`: `aₖ` for `k < n`, zero
beyond.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public def digitSeq {n b : ℕ} (a : Fin n → Fin b) : ℕ → ℕ :=
  fun k => if hk : k < n then (a ⟨k, hk⟩ : ℕ) else 0

/-- Digits beyond the length of the string vanish.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public theorem digitSeq_of_le {n b : ℕ} (a : Fin n → Fin b) {k : ℕ} (hk : n ≤ k) :
    digitSeq a k = 0 := by
  simp [digitSeq, Nat.not_lt.2 hk]

/-- The lunar multiplicative unit of base `b`: the constant polynomial `b - 1`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public def lunarUnit (b : ℕ) : ℕ → ℕ :=
  fun k => if k = 0 then b - 1 else 0

/-- For `b ≥ 2` the lunar unit is a monomial.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public theorem isMaxMinMonomial_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsMaxMinMonomial (lunarUnit b) :=
  ⟨0, fun j => by by_cases hj : j = 0 <;> simp [lunarUnit, hj]; omega⟩

/-- A prime lunar number of base `b` (Applegate, LeBrun and Sloane): every factorization
`f = g ⊗ h` with `g, h ∈ ℬ_b[x]` (coefficients below `b`) has `g` or `h` equal to the unit
`b - 1`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public def IsLunarPrime (b : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, (∀ i, g i < b) → (∀ i, h i < b) → maxMinMul g h = f →
    g = lunarUnit b ∨ h = lunarUnit b

/-- For `b ≥ 2` the zero sequence is not a lunar prime: `0 = 0 ⊗ 0`.

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

/-- A prime candidate of `ℬ_b[x]`: nonzero constant term and maximum coefficient `b - 1` (for
coefficients below `b`, some coefficient equals `b - 1`).

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public def IsLunarPrimeCandidate (b : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 ≠ 0 ∧ ∃ i, f i = b - 1

/-- The unit `b - 1` is a prime candidate when `b ≥ 2`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public theorem isLunarPrimeCandidate_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsLunarPrimeCandidate b (lunarUnit b) :=
  ⟨by simp [lunarUnit]; omega, 0, by simp [lunarUnit]⟩

/-- Theorem 10 (Shitov): as `n → ∞`, the proportion of degree-`n` Boolean polynomials (lunar
numbers of `ℒ_2`) with nonzero constant term which are prime tends to `1`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 10
(`jis-2025-25.2.7-thm-10`), quoting Shitov (2014), Theorem 2.5. -/
public theorem_wanted shitov_boolean_prime_density :
    Tendsto (fun n : ℕ =>
      ({a : Fin (n + 1) → Fin 2 | digitSeq a n ≠ 0 ∧ digitSeq a 0 ≠ 0 ∧
          IsLunarPrime 2 (digitSeq a)}.ncard : ℝ) /
        ({a : Fin (n + 1) → Fin 2 | digitSeq a n ≠ 0 ∧ digitSeq a 0 ≠ 0}.ncard : ℝ))
      atTop (𝓝 1)

/-- Theorem 11: for every integer `b ≥ 2`, the proportion of degree-`n` polynomials over
`ℬ_b = {0, …, b - 1}` which are indecomposable tends to `1` as `n → ∞`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 11
(`jis-2025-25.2.7-thm-11`). -/
public theorem_wanted maxMin_indecomposable_density {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ =>
      ({a : Fin (n + 1) → Fin b | digitSeq a n ≠ 0 ∧ IsMaxMinIndecomposable (digitSeq a)}.ncard
          : ℝ) /
        ({a : Fin (n + 1) → Fin b | digitSeq a n ≠ 0}.ncard : ℝ))
      atTop (𝓝 1)

/-- Corollary 12 (conjecture of Applegate, LeBrun and Sloane): for fixed `b ≥ 2`, the number
`π_b(n)` of prime lunar numbers of `ℒ_b` with `n` digits (degree `n - 1`) satisfies
`π_b(n) ∼ (b - 1)² bⁿ⁻²`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Corollary 12
(`jis-2025-25.2.7-cor-12`). -/
public theorem_wanted lunar_prime_count_isEquivalent {b : ℕ} (hb : 2 ≤ b) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ =>
        ({a : Fin n → Fin b | digitSeq a (n - 1) ≠ 0 ∧ IsLunarPrime b (digitSeq a)}.ncard : ℝ))
      (fun n : ℕ => ((b : ℝ) - 1) ^ 2 * (b : ℝ) ^ n / (b : ℝ) ^ 2)

/-- Theorem 15 (Applegate, LeBrun and Sloane, prime promotion): a digit map `d` (a nondecreasing
map on digits) commutes with lunar addition (pointwise maximum) and lunar multiplication
(max-min convolution): `d(f) ⊕ d(g) = d(f ⊕ g)` and `d(f) ⊗ d(g) = d(f ⊗ g)`. Stated for every
monotone `d : ℕ → ℕ` and all coefficient sequences; a base-`b` digit map extends to such a `d`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 15
(`jis-2025-25.2.7-thm-15`). -/
public theorem_wanted digitMap_lunar_hom {d : ℕ → ℕ} (hd : Monotone d) (f g : ℕ → ℕ) :
    (d ∘ f) ⊔ (d ∘ g) = d ∘ (f ⊔ g) ∧ maxMinMul (d ∘ f) (d ∘ g) = d ∘ maxMinMul f g

/-- Lemma 19: for every real `d > 0`, the number of pairs of Boolean polynomials `(f, g)`, here
their supports `(A, B)`, with nonzero constant term of `f` (`0 ∈ A`), `deg f = k > 0`,
`deg g = n - k`, and `|f ⊗ g| ≤ |f| + |g| + d` (`|A + B| ≤ |A| + |B| + d`) is at most
`n^{2d+2} 2^k`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 19
(`jis-2025-25.2.7-lem-19`). -/
public theorem_wanted boolean_close_factor_pairs_card_le {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {d : ℝ} (hd : 0 < d) :
    ({p : Finset ℕ × Finset ℕ | 0 ∈ p.1 ∧ k ∈ p.1 ∧ (∀ x ∈ p.1, x ≤ k) ∧
        n - k ∈ p.2 ∧ (∀ y ∈ p.2, y ≤ n - k) ∧
        ((p.1 + p.2).card : ℝ) ≤ p.1.card + p.2.card + d}.ncard : ℝ) ≤
      (n : ℝ) ^ (2 * d + 2) * 2 ^ k

/-- Lemma 30 (Applegate, LeBrun and Sloane): an indecomposable prime candidate of `ℬ_b[x]` is
prime.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 30
(`jis-2025-25.2.7-lem-30`). -/
public theorem_wanted isLunarPrime_of_indecomposable_candidate {n b : ℕ} (hb : 2 ≤ b)
    (a : Fin n → Fin b) (hc : IsLunarPrimeCandidate b (digitSeq a))
    (hi : IsMaxMinIndecomposable (digitSeq a)) :
    IsLunarPrime b (digitSeq a)


/-- `|f_i|` for a lunar number of degree at most `n` given by its digit string
`f : Fin (n + 1) → Fin b`: the number of coefficients `≥ i`, i.e. the number of nonzero
coefficients of the `i`-level support `f_i = s_i(f)` (Definitions 13 and 16). A lunar number is
not a monomial `t xᵐ` (`t = 0` allowed) iff `2 ≤ lunarLevelCount 1 f`, and `f_i` is not a
monomial iff `2 ≤ lunarLevelCount i f`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, Definitions 13 and 16. -/
public def lunarLevelCount {n b : ℕ} (i : ℕ) (f : Fin (n + 1) → Fin b) : ℕ :=
  (Finset.univ.filter fun k => i ≤ (f k : ℕ)).card

/-- For `f = 1 ⊕ 2x²` in base `3`: `|f_1| = 2` and `|f_2| = 1`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, Definitions 13 and 16. -/
public theorem lunarLevelCount_example :
    lunarLevelCount 1 (![1, 0, 2] : Fin 3 → Fin 3) = 2 ∧
      lunarLevelCount 2 (![1, 0, 2] : Fin 3 → Fin 3) = 1 := by
  decide

/-- The decomposable lunar numbers `Σ_b^n` of degree at most `n`: `h = f ⊗ g` with `f, g` not
monomials (a monomial is `t xᵐ` with `t ∈ {0, …, b - 1}`, so a non-monomial has at least two
nonzero coefficients). Factors range over `ℒ_b^n`, which contains every factor of a nonzero
`h` of degree at most `n`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Proposition 21. -/
public def lunarDecomposableSet (b n : ℕ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount 1 f ∧ 2 ≤ lunarLevelCount 1 g ∧
    maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}

/-- `𝒟_b^n ⊆ Σ_b^n`: the `h` with a factorization `h = f ⊗ g` such that `f_a, g_a` are not
monomials, `a = ⌊b/2⌋`; then `ℐ_b^n = Σ_b^n \ 𝒟_b^n`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Remark 22. -/
public def lunarLevelDecomposableSet (b n : ℕ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount (b / 2) f ∧
    2 ≤ lunarLevelCount (b / 2) g ∧ maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}

/-- The `d`-Hoeffding extremal lunar numbers `ℋ_b^n(d)` (Definition 23): `h ∈ ℒ_b^n` such that
for some `1 ≤ i ≤ b - 1`, `||h_i| - (b - i)n/b| > d/2`, or `h` has a factorization
`h = f ⊗ g` with `||f_i| + |g_i| - (b - i)(n + 1)/b| > d/2`. Factors range over `ℒ_b^n`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Definition 23. -/
public def lunarHoeffdingExtremalSet (b n : ℕ) (d : ℝ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ i, 1 ≤ i ∧ i ≤ b - 1 ∧
    (d / 2 < |(lunarLevelCount i h : ℝ) - ((b : ℝ) - i) * n / b| ∨
      ∃ f g : Fin (n + 1) → Fin b, maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i f + lunarLevelCount i g : ℕ) : ℝ) -
          ((b : ℝ) - i) * (n + 1) / b|)}

private theorem digitSeq_one_one_zero_mul :
    maxMinMul (digitSeq (![1, 1, 0] : Fin 3 → Fin 2)) (digitSeq (![1, 1, 0] : Fin 3 → Fin 2)) =
      digitSeq (![1, 1, 1] : Fin 3 → Fin 2) := by
  funext k
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · have h1 : digitSeq (![1, 1, 1] : Fin 3 → Fin 2) (k + 3) = 0 := digitSeq_of_le _ (by omega)
    rw [h1, maxMinMul]
    refine le_antisymm (Finset.sup_le fun p hp => ?_) (Nat.zero_le _)
    rw [Finset.mem_antidiagonal] at hp
    have : 2 ≤ p.1 ∨ 2 ≤ p.2 := by omega
    rcases this with h | h
    · have : digitSeq (![1, 1, 0] : Fin 3 → Fin 2) p.1 = 0 := by
        rcases Nat.lt_or_ge p.1 3 with h3 | h3
        · rw [show p.1 = 2 by omega]
          decide
        · exact digitSeq_of_le _ h3
      simp [this]
    · have : digitSeq (![1, 1, 0] : Fin 3 → Fin 2) p.2 = 0 := by
        rcases Nat.lt_or_ge p.2 3 with h3 | h3
        · rw [show p.2 = 2 by omega]
          decide
        · exact digitSeq_of_le _ h3
      simp [this]

/-- In base `2`, `1 ⊕ x ⊕ x² = (1 ⊕ x) ⊗ (1 ⊕ x)` lies in `Σ_2^2` and in `𝒟_2^2`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Proposition 21 and Remark 22. -/
public theorem mem_lunarDecomposableSet_example :
    (![1, 1, 1] : Fin 3 → Fin 2) ∈ lunarDecomposableSet 2 2 ∧
      (![1, 1, 1] : Fin 3 → Fin 2) ∈ lunarLevelDecomposableSet 2 2 :=
  ⟨⟨![1, 1, 0], ![1, 1, 0], by decide, by decide, digitSeq_one_one_zero_mul⟩,
    ⟨![1, 1, 0], ![1, 1, 0], by decide, by decide, digitSeq_one_one_zero_mul⟩⟩

/-- In base `2` and degree at most `2`, the zero lunar number is `1`-Hoeffding extremal:
`||0_1| - 2/2| = 1 > 1/2`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Definition 23. -/
public theorem zero_mem_lunarHoeffdingExtremalSet :
    (0 : Fin 3 → Fin 2) ∈ lunarHoeffdingExtremalSet 2 2 1 := by
  refine ⟨1, le_rfl, le_rfl, Or.inl ?_⟩
  have : lunarLevelCount 1 (0 : Fin 3 → Fin 2) = 0 := by decide
  rw [this]
  norm_num

/-- Proposition 21: for fixed `b ≥ 2` there is `C > 0` such that for all `n ≥ 2` and
`d, v > 0`,
`|Σ_b^n| ≤ C b^{n+1} (n² e^{-d²/(4(n+2))} + n^{2d+4} 2^{d/2-(n+1)/3}
  + v n^{2d+2} 2^v b^{d/2-n/b} + n² 2^{-v})`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Proposition 21 (`jis-2025-25.2.7-prop-21`). -/
public theorem_wanted lunarDecomposableSet_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ d v : ℝ, 0 < d → 0 < v →
      ((lunarDecomposableSet b n).ncard : ℝ) ≤ C * (b : ℝ) ^ (n + 1) *
        ((n : ℝ) ^ 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) +
          (n : ℝ) ^ (2 * d + 4) * (2 : ℝ) ^ (d / 2 - (n + 1) / 3) +
          v * (n : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ v * (b : ℝ) ^ (d / 2 - n / b) +
          (n : ℝ) ^ 2 * (2 : ℝ) ^ (-v))

/-- Lemma 24: for fixed `b ≥ 2` there is `C > 0` such that
`|ℋ_b^n(d)| ≤ C n² e^{-d²/(4(n+2))} bⁿ` for all `n ≥ 1` and `d > 0`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 24 (`jis-2025-25.2.7-lem-24`). -/
public theorem_wanted lunarHoeffdingExtremalSet_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ d : ℝ, 0 < d →
      ((lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
        C * (n : ℝ) ^ 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n

/-- Lemma 25: if `h = f ⊗ g` is not `d`-Hoeffding extremal and `1 ≤ i ≤ b - 1`, then
`|h_i| ≤ |f_i| + |g_i| + d` (the source prints `|b_i|` for `|g_i|`; its hypothesis
`h ∈ Σ_b^n` is not needed).

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 25 (`jis-2025-25.2.7-lem-25`). -/
public theorem_wanted lunarLevelCount_le_of_not_mem_lunarHoeffdingExtremalSet {b n : ℕ} {d : ℝ}
    {f g h : Fin (n + 1) → Fin b} (hfg : maxMinMul (digitSeq f) (digitSeq g) = digitSeq h)
    (hH : h ∉ lunarHoeffdingExtremalSet b n d) {i : ℕ} (hi : 1 ≤ i) (hib : i ≤ b - 1) :
    (lunarLevelCount i h : ℝ) ≤ lunarLevelCount i f + lunarLevelCount i g + d

/-- Lemma 26: for `b ≥ 2` and `d > 0`, `|𝒟_b^n \ ℋ_b^n(d)| ≤ n^{2d+4} 2^{d/2-n/3} b^{n+1}`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 26 (`jis-2025-25.2.7-lem-26`). -/
public theorem_wanted lunarLevelDecomposableSet_diff_ncard_le {b : ℕ} (hb : 2 ≤ b) (n : ℕ)
    {d : ℝ} (hd : 0 < d) :
    ((lunarLevelDecomposableSet b n \ lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
      (n : ℝ) ^ (2 * d + 4) * (2 : ℝ) ^ (d / 2 - n / 3) * (b : ℝ) ^ (n + 1)

/-- Lemma 27: for `b ≥ 2` and `d, v > 0`, the number of `h ∈ Σ_b^n \ ℋ_b^n(d)` with a
nontrivial factorization `h = f ⊗ g` (`f, g` not monomials) with `deg f ≤ v` is at most
`v n^{2d+3} 2^v (b - 1)^{(b-1)n/b + d/2}`. The factorization is nontrivial as in the source's
proof; if trivial factorizations counted (`h = (b - 1) ⊗ h`, `deg (b - 1) = 0`), the claim
fails at `b = 2`, `n = 2`, `d = 5`, `v = 10⁻⁴`: `1 ⊕ x ⊕ x² ∈ Σ_2^2 \ ℋ_2^2(5)` but the bound
is `8192 · 10⁻⁴ · 2^{10⁻⁴} < 1`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 27 (`jis-2025-25.2.7-lem-27`). -/
public theorem_wanted lunar_low_degree_factor_ncard_le {b : ℕ} (hb : 2 ≤ b) (n : ℕ) {d v : ℝ}
    (hd : 0 < d) (hv : 0 < v) :
    ({h | h ∈ lunarDecomposableSet b n \ lunarHoeffdingExtremalSet b n d ∧
        ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount 1 f ∧ 2 ≤ lunarLevelCount 1 g ∧
          (∀ k : Fin (n + 1), v < (k : ℝ) → (f k : ℕ) = 0) ∧
          maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}.ncard : ℝ) ≤
      v * (n : ℝ) ^ (2 * d + 3) * (2 : ℝ) ^ v * ((b : ℝ) - 1) ^ (((b : ℝ) - 1) * n / b + d / 2)

/-- Lemma 28: for fixed `b ≥ 2` there is `C > 0` such that for all `n` and `d, v > 0`,
`|ℐ_b^n \ ℋ_b^n(d)| ≤ C (v n^{2d+2} 2^v b^{(b-1)n/b + d/2} + n² 2^{-v} b^{n+1})`, where
`ℐ_b^n = Σ_b^n \ 𝒟_b^n`.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 28 (`jis-2025-25.2.7-lem-28`). -/
public theorem_wanted lunarIndecomposableLevel_diff_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ d v : ℝ, 0 < d → 0 < v →
      (((lunarDecomposableSet b n \ lunarLevelDecomposableSet b n) \
          lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
        C * (v * (n : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ v *
            (b : ℝ) ^ (((b : ℝ) - 1) * n / b + d / 2) +
          (n : ℝ) ^ 2 * (2 : ℝ) ^ (-v) * (b : ℝ) ^ (n + 1))

end

end MetaMathlibExt
