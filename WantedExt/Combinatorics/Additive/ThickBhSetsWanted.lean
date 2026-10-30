/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Combinatorics.Additive.BhSet

/-!
# Constructing thick `B_h`-sets

Statements from Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer
Sequences 27 (2024), Article 24.1.2 (arXiv:2308.12406): the generalized Bose and Singer
constructions of `B_h`-sets in cyclic groups, sufficient conditions for two such sets to be
affinely equivalent, the prime-gap results the paper quotes, and the resulting bounds on
`R_h(n)` and `R_h⁻¹(k)`.

The paper fixes the generator `θ` to be a root of a Conway polynomial; the statements here
are made for every generator `θ` of `K^×`, which is what the paper's proofs use. Residues
`b ∈ ℤ/Mℤ` are represented by natural numbers `b`, since `θ ^ b` depends only on `b mod M`.
-/

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- The generalized Bose set `Bose_h(q, b)`: for a finite field `F` with `q` elements, an
extension `K` of degree `h`, a generator `θ` of `K^×` and an exponent `b`, the residues
`a ∈ ℤ/(q^h - 1)ℤ` with `θ^a = θ^b + v` for some `v ∈ F`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 1. -/
public def boseSet (F : Type*) {K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) : Set (ZMod (Fintype.card F ^ h - 1)) :=
  {a | ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v}

/-- Membership in `boseSet` unfolds to its defining equation.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 1. -/
public theorem mem_boseSet {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) (a : ZMod (Fintype.card F ^ h - 1)) :
    a ∈ boseSet F h θ b ↔ ∃ v : F, θ ^ a.val = θ ^ b + algebraMap F K v :=
  Iff.rfl

/-- The generalized Singer set `Singer_h(q, b)`: for a finite field `F` with `q` elements,
an extension `K` of degree `h + 1`, a generator `θ` of `K^×` and an exponent `b`, the
residues `a ∈ ℤ/Mℤ`, `M = (q^(h+1) - 1)/(q - 1)`, with `θ^a = uθ^b + v` for some
`u, v ∈ F`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 2. -/
public def singerSet (F : Type*) {K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ) :
    Set (ZMod ((Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1))) :=
  {a | ∃ u v : F, θ ^ a.val = algebraMap F K u * θ ^ b + algebraMap F K v}

/-- Membership in `singerSet` unfolds to its defining equation.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Definition 2. -/
public theorem mem_singerSet {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    (h : ℕ) (θ : K) (b : ℕ)
    (a : ZMod ((Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1))) :
    a ∈ singerSet F h θ b ↔
      ∃ u v : F, θ ^ a.val = algebraMap F K u * θ ^ b + algebraMap F K v :=
  Iff.rfl

/-- Sets `A₁, A₂ ⊆ ℤ/Mℤ` are affinely equivalent, `A₁ ∼ A₂`, if `A₂ = {d a + s : a ∈ A₁}`
for some unit `d` and some `s`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition before Theorem 4. -/
public def ZModAffinelyEquivalent {M : ℕ} (A₁ A₂ : Set (ZMod M)) : Prop :=
  ∃ d s : ZMod M, IsUnit d ∧ A₂ = (fun a => d * a + s) '' A₁

/-- Every set is affinely equivalent to itself (take `d = 1`, `s = 0`).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition before Theorem 4. -/
public theorem zModAffinelyEquivalent_refl {M : ℕ} (A : Set (ZMod M)) :
    ZModAffinelyEquivalent A A :=
  ⟨1, 0, isUnit_one, by simp⟩

/-- `R_h(n)`: the largest cardinality of a `B_h`-set contained in `{1, …, n}`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 5. -/
public noncomputable def bhMaxCard (h n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧
    AdditiveCombinatorics.IsBhSet (A : Set ℕ) h ∧ A.card = k}

/-- `R_h⁻¹(k)`: the smallest `n` such that some `B_h`-set with `k` elements is contained in
`{1, …, n}`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 5. -/
public noncomputable def bhMinLength (h k : ℕ) : ℕ :=
  sInf {n | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧
    AdditiveCombinatorics.IsBhSet (A : Set ℕ) h ∧ A.card = k}

private theorem isBhSet_singleton {h : ℕ} (hh : 0 < h) (a : ℕ) :
    AdditiveCombinatorics.IsBhSet ({a} : Set ℕ) h := by
  refine ⟨Set.singleton_nonempty a, hh, ?_⟩
  intro l₁ l₂ h₁ h₂ len₁ len₂ _ _ _
  rw [List.eq_replicate_iff.2 ⟨len₁, fun x hx => h₁ x hx⟩,
    List.eq_replicate_iff.2 ⟨len₂, fun x hx => h₂ x hx⟩]

/-- `R_h(n) ≤ n`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition of `R_h(n)` before Theorem 5. -/
public theorem bhMaxCard_le (h n : ℕ) : bhMaxCard h n ≤ n := by
  refine csSup_le' ?_
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- `R_h(1) = 1` for `h ≥ 1`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the definition of `R_h(n)` before Theorem 5. -/
public theorem bhMaxCard_one {h : ℕ} (hh : 0 < h) : bhMaxCard h 1 = 1 := by
  refine le_antisymm (bhMaxCard_le h 1) ?_
  refine le_csSup ⟨1, ?_⟩ ⟨{1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- `R_h⁻¹(1) = 1` for `h ≥ 1`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, the paragraph before Theorem 7 ("Clearly, `R_h⁻¹(1) = 1`"). -/
public theorem bhMinLength_one {h : ℕ} (hh : 0 < h) : bhMinLength h 1 = 1 := by
  refine le_antisymm
    (Nat.sInf_le ⟨{1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩) ?_
  rw [Nat.one_le_iff_ne_zero, Ne, bhMinLength, Nat.sInf_eq_zero, not_or]
  refine ⟨?_, Set.nonempty_iff_ne_empty.1
    ⟨1, {1}, by simp, by simpa using isBhSet_singleton hh 1, rfl⟩⟩
  rintro ⟨A, hA, -, hcard⟩
  have : A = ∅ := by simpa using hA
  simp [this] at hcard

/-- **Theorem 3, Bose part.** If `h ≥ 2`, `K` is a degree-`h` extension of the finite field
`F` with `q` elements, `θ` generates `K^×`, and `θ^b` has degree `h` over `F`, then
`Bose_h(q, b)` is a `B_h`-set in `ℤ/(q^h - 1)ℤ` with exactly `q` elements.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 3 (first sentence) (`jis-2024-24.1.2-thm-3`). -/
public theorem_wanted isBhSet_boseSet {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) :
    AdditiveCombinatorics.IsBhSet (boseSet F h θ b) h ∧
      (boseSet F h θ b).ncard = Fintype.card F

/-- **Theorem 3, Singer part.** If `h ≥ 2`, `K` is a degree-`(h + 1)` extension of the finite
field `F` with `q` elements, `θ` generates `K^×`, and `θ^b` has degree `h + 1` over `F`,
then `Singer_h(q, b)` is a `B_h`-set in `ℤ/((q^(h+1) - 1)/(q - 1))ℤ` with exactly `q + 1`
elements.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 3 (second sentence) (`jis-2024-24.1.2-thm-3`). -/
public theorem_wanted isBhSet_singerSet {F K : Type*} [Field F] [Fintype F] [Field K]
    [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h + 1) {θ : K}
    (hθ : orderOf θ = Fintype.card K - 1) {b : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h + 1) :
    AdditiveCombinatorics.IsBhSet (singerSet F h θ b) h ∧
      (singerSet F h θ b).ncard = Fintype.card F + 1

/-- **Theorem 4, Bose part.** With `q = |F|` and `p` the characteristic of `F`, and `b, e`
both admissible for `Bose_h`, each of (i) `b ≡ e (mod (q^h - 1)/(q - 1))`,
(ii) `θ^b - θ^e ∈ F`, (iii) `b ≡ p^i e (mod q^h - 1)` for some `i`, implies
`Bose_h(q, b) ∼ Bose_h(q, e)`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 4 (items (i)–(iii)) (`jis-2024-24.1.2-thm-4`). -/
public theorem_wanted zModAffinelyEquivalent_boseSet {F K : Type*} [Field F] [Fintype F]
    [Field K] [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h) (hK : Module.finrank F K = h)
    {θ : K} (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h) (he : (minpoly F (θ ^ e)).natDegree = h)
    (hbe : b ≡ e [MOD (Fintype.card F ^ h - 1) / (Fintype.card F - 1)] ∨
      θ ^ b - θ ^ e ∈ Set.range (algebraMap F K) ∨
      ∃ i : ℕ, b ≡ ringChar F ^ i * e [MOD Fintype.card F ^ h - 1]) :
    ZModAffinelyEquivalent (boseSet F h θ b) (boseSet F h θ e)

/-- **Theorem 4, Singer part.** With `q = |F|`, `p` the characteristic of `F`,
`M = (q^(h+1) - 1)/(q - 1)`, and `b, e` both admissible for `Singer_h`, each of
(iv) `b ≡ e (mod M)`, (v) `b ≡ p^i e (mod q^(h+1) - 1)` for some `i`, (vi) `θ^b - θ^e ∈ F`,
(vii) `rθ^b + tθ^(e+b) + wθ^e ∈ F` for some `r, t, w ∈ F` with `r, t` not both `0`,
implies `Singer_h(q, b) ∼ Singer_h(q, e)`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 4 (items (iv)–(vii)) (`jis-2024-24.1.2-thm-4`). -/
public theorem_wanted zModAffinelyEquivalent_singerSet {F K : Type*} [Field F] [Fintype F]
    [Field K] [Fintype K] [Algebra F K] {h : ℕ} (hh : 2 ≤ h)
    (hK : Module.finrank F K = h + 1) {θ : K} (hθ : orderOf θ = Fintype.card K - 1) {b e : ℕ}
    (hb : (minpoly F (θ ^ b)).natDegree = h + 1)
    (he : (minpoly F (θ ^ e)).natDegree = h + 1)
    (hbe : b ≡ e [MOD (Fintype.card F ^ (h + 1) - 1) / (Fintype.card F - 1)] ∨
      (∃ i : ℕ, b ≡ ringChar F ^ i * e [MOD Fintype.card F ^ (h + 1) - 1]) ∨
      θ ^ b - θ ^ e ∈ Set.range (algebraMap F K) ∨
      ∃ r t w : F, (r ≠ 0 ∨ t ≠ 0) ∧
        algebraMap F K r * θ ^ b + algebraMap F K t * θ ^ (e + b) +
          algebraMap F K w * θ ^ e ∈ Set.range (algebraMap F K)) :
    ZModAffinelyEquivalent (singerSet F h θ b) (singerSet F h θ e)

/-- **Theorem 5(a).** For `h ≥ 2` and all `n, k ∈ ℕ`,
`R_h(n) ≥ n^(1/h) - 2^44 n^(154/(155h))` and `R_h⁻¹(k) ≤ k^h + 3^(155h) k^(h - 1/155)`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(a) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_unconditional {h : ℕ} (hh : 2 ≤ h) :
    (∀ n : ℕ, (n : ℝ) ^ (1 / (h : ℝ)) - 2 ^ 44 * (n : ℝ) ^ ((154 : ℝ) / (155 * h)) ≤
      bhMaxCard h n) ∧
    ∀ k : ℕ, (bhMinLength h k : ℝ) ≤
      (k : ℝ) ^ h + 3 ^ (155 * h) * (k : ℝ) ^ ((h : ℝ) - 1 / 155)

/-- **Theorem 5(b).** For `h ≥ 2`, if `n ≥ e^(e^34)` then `R_h(n) ≥ n^(1/h) - 7 n^(2/(3h))`,
and if `k ≥ e^(e^34)` then `R_h⁻¹(k) ≤ k^h + (3k)^(h - 1/3)`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(b) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_large {h : ℕ} (hh : 2 ≤ h) :
    (∀ n : ℕ, Real.exp (Real.exp 34) ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 7 * (n : ℝ) ^ ((2 : ℝ) / (3 * h)) ≤ bhMaxCard h n) ∧
    ∀ k : ℕ, Real.exp (Real.exp 34) ≤ k →
      (bhMinLength h k : ℝ) ≤ (k : ℝ) ^ h + (3 * k : ℝ) ^ ((h : ℝ) - 1 / 3)

/-- **Theorem 5(c).** For `h ≥ 2`, for all sufficiently large `n`,
`R_h(n) ≥ n^(1/h) - n^(21/(40h))`, and for all sufficiently large `k`,
`R_h⁻¹(k) ≤ k^h + 2^h k^(h - 19/40)`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(c) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_eventually {h : ℕ} (hh : 2 ≤ h) :
    (∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / (h : ℝ)) - (n : ℝ) ^ ((21 : ℝ) / (40 * h)) ≤ bhMaxCard h n) ∧
    ∀ᶠ k : ℕ in atTop,
      (bhMinLength h k : ℝ) ≤ (k : ℝ) ^ h + 2 ^ h * (k : ℝ) ^ ((h : ℝ) - 19 / 40)

/-- **Theorem 5(d).** Assuming the Riemann Hypothesis, for `h ≥ 2`, all `k ≥ 1` and all `n`,
`R_h⁻¹(k) < k^h + log(20k) k^(h - 1/2) + 2k^(h-1) log^(2h)(20k)` and
`R_h(n) ≥ n^(1/h) - (7 + (log n)/h) n^(1/(2h))`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 5(d) (`jis-2024-24.1.2-thm-5`). -/
public theorem_wanted bhMaxCard_bhMinLength_bounds_of_RH (hRH : RiemannHypothesis) {h : ℕ}
    (hh : 2 ≤ h) :
    (∀ k : ℕ, 1 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + Real.log (20 * k) * (k : ℝ) ^ ((h : ℝ) - 1 / 2) +
        2 * (k : ℝ) ^ (h - 1) * Real.log (20 * k) ^ (2 * h)) ∧
    ∀ n : ℕ, (n : ℝ) ^ (1 / (h : ℝ)) - (7 + Real.log n / h) * (n : ℝ) ^ (1 / (2 * (h : ℝ))) ≤
      bhMaxCard h n

/-- **Cully-Hugill's theorem** (as quoted in the paper): for every integer `n ≥ 1` there is
a prime strictly between `n^155` and `(n + 1)^155`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 6 (Cully-Hugill) (`jis-2024-24.1.2-thm-6`). -/
public theorem_wanted exists_prime_between_pow_155 (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 155 < p ∧ p < (n + 1) ^ 155

/-- **Theorem 7.** For `h ≥ 2`, all `k ≥ 4` and all `n ≥ h + 3`,
`R_h⁻¹(k) < k^h + 3^(155h) k^(h - 1/155)` and `R_h(n) ≥ n^(1/h) - 2^44 n^(154/(155h))`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 7 (`jis-2024-24.1.2-thm-7`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_explicit {h : ℕ} (hh : 2 ≤ h) :
    (∀ k : ℕ, 4 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + 3 ^ (155 * h) * (k : ℝ) ^ ((h : ℝ) - 1 / 155)) ∧
    ∀ n : ℕ, h + 3 ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 2 ^ 44 * (n : ℝ) ^ ((154 : ℝ) / (155 * h)) ≤ bhMaxCard h n

/-- **Cully-Hugill's theorem for cubes** (as quoted in the paper): for every integer
`n > exp(exp(32.537))` there is a prime strictly between `n^3` and `(n + 1)^3`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 8 (Cully-Hugill) (`jis-2024-24.1.2-thm-8`). -/
public theorem_wanted exists_prime_between_cubes_of_large (n : ℕ)
    (hn : Real.exp (Real.exp 32.537) < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

/-- **Theorem 9.** For `h ≥ 2`, if `k > e^(e^34)` then `R_h⁻¹(k) < k^h + (3k)^(h - 1/3)`, and
if `n > e^(e^34)` then `R_h(n) > n^(1/h) - 7 n^(2/(3h))`. The printed theorem leaves `n`
unquantified; the hypothesis on `n` is taken from Theorem 5(b).

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 9 (`jis-2024-24.1.2-thm-9`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_gt_large {h : ℕ} (hh : 2 ≤ h) :
    (∀ k : ℕ, Real.exp (Real.exp 34) < k →
      (bhMinLength h k : ℝ) < (k : ℝ) ^ h + (3 * k : ℝ) ^ ((h : ℝ) - 1 / 3)) ∧
    ∀ n : ℕ, Real.exp (Real.exp 34) < n →
      (n : ℝ) ^ (1 / (h : ℝ)) - 7 * (n : ℝ) ^ ((2 : ℝ) / (3 * h)) < bhMaxCard h n

/-- **Baker–Harman–Pintz** (as quoted in the paper): for all sufficiently large real `x`
there is a prime in `[x - x^(21/40), x]` and a prime in `[x, x + x^(21/40)]`. The paper prints
the first interval as `[x - x^(21/40), n]` with `n` undefined; the right endpoint is read as `x`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 10 (Baker, Harman and Pintz) (`jis-2024-24.1.2-thm-10`). -/
public theorem_wanted eventually_exists_prime_short_intervals :
    ∀ᶠ x : ℝ in atTop,
      (∃ p : ℕ, p.Prime ∧ x - x ^ ((21 : ℝ) / 40) ≤ p ∧ (p : ℝ) ≤ x) ∧
      ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + x ^ ((21 : ℝ) / 40)

/-- **Theorem 11.** For `h ≥ 2`, for all sufficiently large `k`,
`R_h⁻¹(k) < k^h + 2^h k^(h - 19/40)`, and for all sufficiently large `n`,
`R_h(n) ≥ n^(1/h) - n^(21/(40h))`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 11 (`jis-2024-24.1.2-thm-11`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_eventually {h : ℕ} (hh : 2 ≤ h) :
    (∀ᶠ k : ℕ in atTop,
      (bhMinLength h k : ℝ) < (k : ℝ) ^ h + 2 ^ h * (k : ℝ) ^ ((h : ℝ) - 19 / 40)) ∧
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / (h : ℝ)) - (n : ℝ) ^ ((21 : ℝ) / (40 * h)) ≤ bhMaxCard h n

/-- **Dudek–Grenié–Molteni** (as quoted in the paper): assuming the Riemann Hypothesis, for
every integer `n ≥ 2` there is a prime strictly between `n^2` and
`(n + (1 + 1/log n)^2 log n)^2`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 12 (`jis-2024-24.1.2-thm-12`). -/
public theorem_wanted exists_prime_between_sq_of_RH (hRH : RiemannHypothesis) (n : ℕ)
    (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ ((n : ℝ) ^ 2 < p) ∧
      (p : ℝ) < ((n : ℝ) + (1 + 1 / Real.log n) ^ 2 * Real.log n) ^ 2

/-- **Theorem 13.** Assuming the Riemann Hypothesis, for `h ≥ 2`, all `k ≥ 4` and all
`n ≥ h + 3`, `R_h⁻¹(k) < k^h + log(20k) k^(h - 1/2) + 2k^(h-1) log^(2h)(20k)` and
`R_h(n) ≥ n^(1/h) - (7 + (log n)/h) n^(1/(2h))`.

Source: Kevin O'Bryant, *Constructing Thick `B_h`-Sets*, Journal of Integer Sequences 27
(2024), Article 24.1.2, Theorem 13 (`jis-2024-24.1.2-thm-13`). -/
public theorem_wanted bhMinLength_lt_and_bhMaxCard_ge_of_RH (hRH : RiemannHypothesis) {h : ℕ}
    (hh : 2 ≤ h) :
    (∀ k : ℕ, 4 ≤ k → (bhMinLength h k : ℝ) <
      (k : ℝ) ^ h + Real.log (20 * k) * (k : ℝ) ^ ((h : ℝ) - 1 / 2) +
        2 * (k : ℝ) ^ (h - 1) * Real.log (20 * k) ^ (2 * h)) ∧
    ∀ n : ℕ, h + 3 ≤ n →
      (n : ℝ) ^ (1 / (h : ℝ)) - (7 + Real.log n / h) * (n : ℝ) ^ (1 / (2 * (h : ℝ))) ≤
        bhMaxCard h n

end

end MetaMathlibExt
