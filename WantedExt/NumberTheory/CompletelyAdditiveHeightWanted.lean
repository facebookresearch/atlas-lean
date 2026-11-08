/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Completely additive height functions

Statements from Hartosh Singh Bal, *Completely Additive Height Functions: Profile
Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116.

A height function is a completely additive `H : ℕ → ℕ` (on positive integers) with `H(p) ≥ 1`
for every prime `p` and only finitely many primes at each height `n ≥ 1`. Primes are indexed
from one: `p₁ = 2, p₂ = 3, …`, so `pᵢ = Nat.nth Nat.Prime (i - 1)`, and the index of a prime `p`
is `Nat.count Nat.Prime p + 1`. Iteratively defined height functions (Matula's
`H(pᵢ) = H(i) + 1`) are stated for every completely additive `H` satisfying the defining
equations, which determine `H` uniquely by strong induction.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace MetaMathlibExt

@[expose] public section

open Filter

/-- Complete additivity on positive integers: `H(ab) = H(a) + H(b)` for all `a, b ≥ 1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public def IsCompletelyAdditiveNat (H : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → H (a * b) = H a + H b

/-- A completely additive function vanishes at `1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public theorem IsCompletelyAdditiveNat.map_one {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    H 1 = 0 := by
  have := hH 1 1 one_pos one_pos
  simp at this
  omega

/-- A height function: completely additive `H : ℕ → ℕ` with `H(1) = 0`, `H(p) ≥ 1` for every
prime `p`, and finitely many primes at each height `n ≥ 1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (definition of a height
function). -/
public structure IsHeightFunction (H : ℕ → ℕ) : Prop where
  additive : IsCompletelyAdditiveNat H
  prime_pos : ∀ p : ℕ, p.Prime → 1 ≤ H p
  finite_primes : ∀ n : ℕ, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.Finite

/-- The `i`-th prime `pᵢ`, indexed from one: `p₁ = 2`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public noncomputable def nthPrimeOne (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime (i - 1)

/-- Small values: `p₁ = 2`, `p₂ = 3`, `p₃ = 5`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 2 (notation `pᵢ`). -/
public theorem nthPrimeOne_one_two_three :
    nthPrimeOne 1 = 2 ∧ nthPrimeOne 2 = 3 ∧ nthPrimeOne 3 = 5 :=
  ⟨Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five⟩

/-- The completely additive function with prescribed prime values `v`:
`m = ∏ p^{aₚ} ↦ ∑ aₚ v(p)`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public noncomputable def additiveOfPrimeValues (v : ℕ → ℕ) (m : ℕ) : ℕ :=
  m.factorization.sum fun p a => a * v p

/-- The extension vanishes at `1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_one (v : ℕ → ℕ) : additiveOfPrimeValues v 1 = 0 := by
  simp [additiveOfPrimeValues]

/-- The extension takes the prescribed value at a prime.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem additiveOfPrimeValues_prime (v : ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    additiveOfPrimeValues v p = v p := by
  simp [additiveOfPrimeValues, hp.factorization]

/-- The extension is completely additive.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3 (extension by complete
additivity). -/
public theorem isCompletelyAdditiveNat_additiveOfPrimeValues (v : ℕ → ℕ) :
    IsCompletelyAdditiveNat (additiveOfPrimeValues v) := by
  intro a b ha hb
  unfold additiveOfPrimeValues
  rw [Nat.factorization_mul ha.ne' hb.ne']
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- Theorem 1 (level construction): for a height function `H` and `n ≥ 1`, the level
`ℋₙ = {m ≥ 1 : H(m) = n}` is the union of the products `p · m'` with `H(p) = ℓ`,
`1 ≤ ℓ ≤ ⌊n/2⌋`, `m' ∈ ℋ_{n-ℓ}`, and the primes of height `n`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 1 (`integers-2026-A116-thm-1`). -/
public theorem_wanted heightLevel_eq_products_union_primes {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {n : ℕ} (hn : 1 ≤ n) :
    {m : ℕ | 0 < m ∧ H m = n} =
      {m : ℕ | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ n / 2 ∧ ∃ p m', p.Prime ∧ H p = ℓ ∧ 0 < m' ∧ H m' = n - ℓ ∧
        m = p * m'} ∪ {p : ℕ | p.Prime ∧ H p = n}

/-- Proposition 1: a height function induces a height-preserving bijection between `ℕ` and
multipartitions with `πₗ` colours at part size `ℓ`, `πₗ` the number of primes of height `ℓ`.
Stated level by level: the number of `m ≥ 1` with `H(m) = n` equals the number of families
`(α_{ℓ,j})`, `1 ≤ ℓ ≤ n`, `j < πₗ`, of nonnegative integers with `∑ ℓ α_{ℓ,j} = n`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 1
(`integers-2026-A116-prop-1`). -/
public theorem_wanted heightLevel_card_eq_multipartitions {H : ℕ → ℕ} (hH : IsHeightFunction H)
    (n : ℕ) :
    Nat.card {m : ℕ // 0 < m ∧ H m = n} =
      Nat.card {α : (Σ ℓ : Fin n, Fin {p : ℕ | p.Prime ∧ H p = ℓ.1 + 1}.ncard) → ℕ //
        ∑ x, (x.1.1 + 1) * α x = n}

/-- Proposition 2 (realizing a prescribed profile): for nonnegative integers `(πₖ)_{k ≥ 1}`
with `∑ πₖ = ∞` (infinitely many `πₖ ≠ 0`), some height function has exactly `πₖ` primes of
height `k` for every `k ≥ 1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 2
(`integers-2026-A116-prop-2`). -/
public theorem_wanted exists_heightFunction_with_profile (π : ℕ → ℕ)
    (hπ : {k : ℕ | 1 ≤ k ∧ π k ≠ 0}.Infinite) :
    ∃ H : ℕ → ℕ, IsHeightFunction H ∧ ∀ k, 1 ≤ k → {p : ℕ | p.Prime ∧ H p = k}.ncard = π k

/-- Proposition 3: if `f : ℕ → ℕ` takes values `≥ 1` on `i ≥ 1` and each value `t ≥ 1` has
finitely many preimages `i ≥ 1`, then the completely additive `H` with `H(pᵢ) = f(i)` is a height
function with `πₙ = #{i ≥ 1 : f(i) = n}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 3
(`integers-2026-A116-prop-3`). -/
public theorem_wanted isHeightFunction_of_finite_fibers (f : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → 1 ≤ f i) (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) :
    let H := additiveOfPrimeValues fun p => f (Nat.count Nat.Prime p + 1)
    IsHeightFunction H ∧
      ∀ n, 1 ≤ n → {p : ℕ | p.Prime ∧ H p = n}.ncard = {i : ℕ | 1 ≤ i ∧ f i = n}.ncard

/-- Proposition 4: for the height function `H(pᵢ) = i`, the largest number at height `n` is
`2ⁿ`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 4
(`integers-2026-A116-prop-4`). -/
public theorem_wanted isGreatest_primeIndexHeight_level (n : ℕ) :
    IsGreatest
      {m : ℕ | 0 < m ∧ additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m = n} (2 ^ n)

/-- The Gutman-Ivić maximal Matula number `P(n)` for `n ≥ 4`: `P(4) = p₈` and
`P(n) = p_{P(n-1)}`, i.e. `n - 3` nested applications of `i ↦ pᵢ` to `8`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public noncomputable def matulaMax (n : ℕ) : ℕ :=
  nthPrimeOne^[n - 3] 8

/-- `P(4) = p₈`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_four : matulaMax 4 = nthPrimeOne 8 :=
  rfl

/-- `P(n + 1) = p_{P(n)}` for `n ≥ 4`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 3.2 (definition of `P(n)`). -/
public theorem matulaMax_succ {n : ℕ} (hn : 4 ≤ n) :
    matulaMax (n + 1) = nthPrimeOne (matulaMax n) := by
  unfold matulaMax
  rw [show n + 1 - 3 = (n - 3) + 1 by omega, Function.iterate_succ_apply']

/-- Proposition 5 (Gutman-Ivić, maximal case): for the Matula height function
`H(pᵢ) = H(i) + 1`, the largest number at height `n ≥ 4` is `P(n)`, attained only by `P(n)`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 5
(`integers-2026-A116-prop-5`). -/
public theorem_wanted matula_isGreatest_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 4 ≤ n) :
    IsGreatest {m : ℕ | 0 < m ∧ H m = n} (matulaMax n)

/-- Proposition 6 (Gutman-Ivić, minimal case): for the Matula height function
`H(pᵢ) = H(i) + 1` and `n > 1`, the smallest number at height `n` is `3 · 5^{(n-2)/3}`,
`5^{n/3}`, or `9 · 5^{(n-4)/3}` according as `n ≡ 2, 0, 1 (mod 3)`, and it is the unique
element of `ℋₙ` with that value (uniqueness of a least element is automatic).

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 6
(`integers-2026-A116-prop-6`). -/
public theorem_wanted matula_isLeast_level {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    (hM : ∀ i, 1 ≤ i → H (nthPrimeOne i) = H i + 1) {n : ℕ} (hn : 1 < n) :
    IsLeast {m : ℕ | 0 < m ∧ H m = n}
      (if n % 3 = 2 then 3 * 5 ^ ((n - 2) / 3)
        else if n % 3 = 0 then 5 ^ (n / 3) else 9 * 5 ^ ((n - 4) / 3))

/-- Lemma 1 (Rosser-Schoenfeld): there is an absolute `k₀` with
`k (log k + log log k - 1) ≤ pₖ ≤ k (log k + log log k)` for all `k ≥ k₀`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 1 (`integers-2026-A116-lem-1`),
quoting Rosser and Schoenfeld. -/
public theorem_wanted nthPrimeOne_rosser_schoenfeld :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (k : ℝ) * (Real.log k + Real.log (Real.log k) - 1) ≤ nthPrimeOne k ∧
        (nthPrimeOne k : ℝ) ≤ k * (Real.log k + Real.log (Real.log k))

/-- Lemma 2: `pₖ > 2k` for all `k ≥ 6`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 2 (`integers-2026-A116-lem-2`). -/
public theorem_wanted two_mul_lt_nthPrimeOne {k : ℕ} (hk : 6 ≤ k) : 2 * k < nthPrimeOne k

/-- Proposition 7 (prime reduction), first identity of Equation (6): for completely additive
`H` and `x ≥ 2`, `F(x) = ∑_{m ≤ x} H(m) = ∑_{p^α ≤ x} H(p) ⌊x / p^α⌋`. Stated for integer `x`
(`F` and every floor depend on `x` only through `⌊x⌋`).

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), Equation (6). -/
public theorem_wanted sum_height_eq_sum_prime_powers {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H)
    {x : ℕ} (hx : 2 ≤ x) :
    ∑ m ∈ Finset.Icc 1 x, H m =
      ∑ p ∈ (Finset.Iic x).filter Nat.Prime,
        ∑ α ∈ (Finset.Icc 1 x).filter (fun α => p ^ α ≤ x), H p * (x / p ^ α)

/-- Proposition 7 (prime reduction), final form: for completely additive `H` there is `C` with
`|F(x) - x ∑_{p ≤ x} H(p)/(p - 1)| ≤ C log x ∑_{p ≤ x} H(p)` for all real `x ≥ 2`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 7
(`integers-2026-A116-prop-7`), "In particular" display. -/
public theorem_wanted sum_height_asymptotic {H : ℕ → ℕ} (hH : IsCompletelyAdditiveNat H) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |(∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (H m : ℝ)) -
          x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ) / ((p : ℝ) - 1)| ≤
        C * Real.log x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (H p : ℝ)

/-- Theorem 2 (iteratively defined height functions): let `f : ℕ → ℕ` with `f(1) = 1` such that
every prime `p_r ∣ f(i)` has `r < i` (which forces `f(i) ≥ 1`), and each value `t ≥ 1` has
finitely many preimages. For `j ≥ 1`, a completely additive `H` with `H(pᵢ) = H(f(i)) + j` for all
`i ≥ 1` exists, and every such `H` is a height function. (`H(2) = j` is the case `i = 1`.)

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 2 (`integers-2026-A116-thm-2`). -/
public theorem_wanted isHeightFunction_of_iterative (f : ℕ → ℕ) (hf1 : f 1 = 1)
    (hdiv : ∀ i r, 1 ≤ i → 1 ≤ r → nthPrimeOne r ∣ f i → r < i)
    (hfin : ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ f i = t}.Finite) {j : ℕ} (hj : 1 ≤ j) :
    (∃ H : ℕ → ℕ, IsCompletelyAdditiveNat H ∧ ∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) ∧
      ∀ H : ℕ → ℕ, IsCompletelyAdditiveNat H → (∀ i, 1 ≤ i → H (nthPrimeOne i) = H (f i) + j) →
        IsHeightFunction H

/-- The coefficients `aₙ` of the weighted partition product `∏_{k ≥ 1} (1 - qᵏ)^{-bₖ}`, computed by
the logarithmic-derivative recurrence `n aₙ = ∑_{m=1}^{n} (∑_{k ∣ m} k bₖ) a_{n-m}`, `a₀ = 1`
(valid for real exponents `bₖ`). The value `b 0` is unused.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public noncomputable def weightedPartitionCoeff (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (∑ m : Fin (n + 1), (∑ k ∈ (m.1 + 1).divisors, (k : ℝ) * b k) *
      weightedPartitionCoeff b (n - m.1)) / (n + 1)
decreasing_by omega

/-- `a₀ = 1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_zero (b : ℕ → ℝ) : weightedPartitionCoeff b 0 = 1 := by
  simp [weightedPartitionCoeff]

/-- `a₁ = b₁`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (weighted partitions
`F(q) = ∑ aₙ qⁿ`). -/
public theorem weightedPartitionCoeff_one (b : ℕ → ℝ) : weightedPartitionCoeff b 1 = b 1 := by
  simp [weightedPartitionCoeff]

/-- Meinardus' hypotheses (M1)-(M3) for weights `(bₖ)_{k ≥ 1}`, exponent `α`, residue `A`, and a
continuation `G` of `B(s) = ∑ bₖ k^{-s}`: (M1) `B` converges for `ℜs > α` and equals `G` there,
and `G(s) = A / (s - α) + R(s)` on `ℜs ≥ -C₀` with `R` holomorphic there, for some
`0 < C₀ < 1`; (M2) `G(σ + it) = O((1 + |t|)^c)` uniformly for `σ ≥ -C₀` as `|t| → ∞`;
(M3) with `g(τ) = ∑ bₖ e^{-kτ}`, `ℜ g(y + 2πix) - g(y) ≤ -C₃ y^{-ε}` for
`y^{1+ε/2} ≤ |x| ≤ 1/2` and all small `y > 0`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 6.1 (hypotheses of Theorem 3). -/
public def MeinardusHypotheses (b : ℕ → ℝ) (α A : ℝ) (G : ℂ → ℂ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ < 1 ∧
    (∀ s : ℂ, α < s.re →
      LSeriesSummable (fun k => (b k : ℂ)) s ∧ LSeries (fun k => (b k : ℂ)) s = G s) ∧
    (∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | -C₀ ≤ s.re} ∧
      ∀ s : ℂ, -C₀ ≤ s.re → s ≠ α → G s = A / (s - α) + R s) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ K T : ℝ, ∀ s : ℂ, -C₀ ≤ s.re → T ≤ |s.im| →
      ‖G s‖ ≤ K * (1 + |s.im|) ^ c) ∧
    (∃ ε C₃ y₀ : ℝ, 0 < ε ∧ 0 < C₃ ∧ 0 < y₀ ∧ ∀ y x : ℝ, 0 < y → y < y₀ →
      y ^ (1 + ε / 2) ≤ |x| → |x| ≤ 1 / 2 →
      (∑' k : ℕ, (b (k + 1) : ℂ) *
          Complex.exp (-((k : ℂ) + 1) * ((y : ℂ) + 2 * Real.pi * Complex.I * x))).re -
        ∑' k : ℕ, b (k + 1) * Real.exp (-((k : ℝ) + 1) * y) ≤ -C₃ * y ^ (-ε))

/-- Theorem 3 (Meinardus): for nonnegative weights `bₖ`, not all zero, satisfying (M1)-(M3) with
`α > 0` and `A > 0`, `aₙ ∼ C₁ n^κ exp(C₂ n^{α/(α+1)})` for some `C₁ > 0`, where
`κ = (B(0) - 1 - α/2)/(α + 1)` (`B(0)` the value of the continuation, real part) and
`C₂ = (1 + 1/α)(A Γ(α + 1) ζ(α + 1))^{1/(α+1)}`; in particular
`log aₙ ∼ C₂ n^{α/(α+1)}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 3 (`integers-2026-A116-thm-3`),
quoting Meinardus. -/
public theorem_wanted meinardus_asymptotic {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hb0 : ∃ k, 1 ≤ k ∧ b k ≠ 0) {α A : ℝ} (hα : 0 < α) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses b α A G) :
    let κ := ((G 0).re - 1 - α / 2) / (α + 1)
    let C₂ := (1 + 1 / α) *
      (A * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop (fun n : ℕ => weightedPartitionCoeff b n)
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop (fun n : ℕ => Real.log (weightedPartitionCoeff b n))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- Lemma 3 (pole data from cumulative profile growth): if `π_k ≥ 0` and
`Π(x) = ∑_{k ≤ x} π_k = (C/α) x^α + O(x^{α-η})` with `C, α, η > 0`, then `B_H(s) = ∑ π_k k^{-s}`
converges for `ℜs > α` and equals `C/(s - α) + R(s)` with `R` holomorphic on `ℜs > α - η`
(a single simple pole at `α`, residue `C`), and for every `δ ∈ (0, η)` the continuation is
`O(1 + |t|)` uniformly on `σ ≥ α - η + δ`, `|t| ≥ 1`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 3 (`integers-2026-A116-lem-3`). -/
public theorem_wanted lseries_profile_simple_pole {π : ℕ → ℝ} (hπ : ∀ k, 0 ≤ π k) {C α η : ℝ}
    (hC : 0 < C) (hα : 0 < α) (hη : 0 < η)
    (hcum : ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      |∑ k ∈ Finset.Icc 1 ⌊x⌋₊, π k - C / α * x ^ α| ≤ K * x ^ (α - η)) :
    (∀ s : ℂ, α < s.re → LSeriesSummable (fun k => (π k : ℂ)) s) ∧
      ∃ R : ℂ → ℂ, DifferentiableOn ℂ R {s | α - η < s.re} ∧
        (∀ s : ℂ, α < s.re → LSeries (fun k => (π k : ℂ)) s = C / (s - α) + R s) ∧
        ∀ δ : ℝ, 0 < δ → δ < η → ∃ K : ℝ, ∀ s : ℂ, α - η + δ ≤ s.re → 1 ≤ |s.im| →
          ‖C / (s - α) + R s‖ ≤ K * (1 + |s.im|)

/-- Theorem 4 (conditional inverse growth): let `H` be a height function with profile
`π_k = #{p : H(p) = k}` and level sizes `Nₙ = #{m ≥ 1 : H(m) = n}`. If the weights `π_k`
satisfy (M1)-(M3) with exponent `α > 0` and residue `C > 0`, then
`Nₙ ∼ C₁ n^κ exp(C₂ n^{α/(α+1)})` for some `C₁ > 0`, `κ ∈ ℝ`, with
`C₂ = (1 + 1/α)(C Γ(α + 1) ζ(α + 1))^{1/(α+1)}`; in particular `log Nₙ ∼ C₂ n^{α/(α+1)}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 4 (`integers-2026-A116-thm-4`). -/
public theorem_wanted heightLevel_card_meinardus {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {α C : ℝ} (hα : 0 < α) (hC : 0 < C) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) α C G) :
    let C₂ := (1 + 1 / α) *
      (C * Real.Gamma (α + 1) * (riemannZeta (α + 1)).re) ^ (1 / (α + 1))
    (∃ C₁ κ : ℝ, 0 < C₁ ∧ Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ (α / (α + 1))))) ∧
      Asymptotics.IsEquivalent atTop
        (fun n : ℕ => Real.log (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
        (fun n : ℕ => C₂ * (n : ℝ) ^ (α / (α + 1)))

/-- Corollary 1 (identification under Meinardus hypotheses): let `H` be a height function whose
profile Dirichlet series satisfies (M1)-(M3) with a simple pole at `r > 0` of residue `A > 0`,
and suppose `Nₙ ∼ C₁ n^κ exp(C₂ n^β)` with `β ∈ (0, 1)`, `C₁, C₂ > 0`. Then `β = r/(r + 1)`,
`r = β/(1 - β)`, `C₂ = (1 + 1/r)(A Γ(r + 1) ζ(r + 1))^{1/(r+1)}`, and
`∑_{k ≤ x} π_k ∼ (A/r) x^r`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 1 (`integers-2026-A116-cor-1`). -/
public theorem_wanted heightProfile_identification {H : ℕ → ℕ} (hH : IsHeightFunction H)
    {r A : ℝ} (hr : 0 < r) (hA : 0 < A) {G : ℂ → ℂ}
    (hM : MeinardusHypotheses (fun k => ({p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ)) r A G)
    {C₁ C₂ κ β : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (Nat.card {m : ℕ // 0 < m ∧ H m = n} : ℝ))
      (fun n : ℕ => C₁ * (n : ℝ) ^ κ * Real.exp (C₂ * (n : ℝ) ^ β))) :
    β = r / (r + 1) ∧ r = β / (1 - β) ∧
      C₂ = (1 + 1 / r) * (A * Real.Gamma (r + 1) * (riemannZeta (r + 1)).re) ^ (1 / (r + 1)) ∧
      Asymptotics.IsEquivalent atTop
        (fun x : ℝ => (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, {p : ℕ | p.Prime ∧ H p = k}.ncard : ℝ))
        (fun x : ℝ => A / r * x ^ r)

/-- The cumulative profile `Π_k = ∑_{j ≤ k} π_j`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public def profilePartialSum (π : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, π j

/-- `Π_{k+1} = Π_k + π_{k+1}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem profilePartialSum_succ (π : ℕ → ℕ) (k : ℕ) :
    profilePartialSum π (k + 1) = profilePartialSum π k + π (k + 1) := by
  simp [profilePartialSum, Finset.sum_Icc_succ_top]

/-- The block index `k(i)`: the least `k` with `i ≤ Π_k` (for `i ≥ 1` and unbounded `Π`, the
unique `k` with `Π_{k-1} < i ≤ Π_k`).

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public noncomputable def seqHeightIndex (π : ℕ → ℕ) (i : ℕ) : ℕ :=
  sInf {k | i ≤ profilePartialSum π k}

/-- For the constant profile `π_k = 1`, `k(i) = i`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Section 7.2 (canonical sequential
realization). -/
public theorem seqHeightIndex_const_one (i : ℕ) : seqHeightIndex (fun _ => 1) i = i := by
  have h : ∀ k, profilePartialSum (fun _ => 1) k = k := fun k => by simp [profilePartialSum]
  simp only [seqHeightIndex, h]
  exact le_antisymm (Nat.sInf_le (show i ≤ i from le_rfl))
    (le_csInf ⟨i, show i ≤ i from le_rfl⟩ fun k hk => hk)

/-- The canonical sequential realization `H_seq` of a profile: `H_seq(pᵢ) = k(i)` and complete
additivity.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Definition 2 (canonical sequential
realization, Section 7.2). -/
public noncomputable def canonicalSeqHeight (π : ℕ → ℕ) : ℕ → ℕ :=
  additiveOfPrimeValues fun p => seqHeightIndex π (Nat.count Nat.Prime p + 1)

/-- Lemma 4 (inverting a polynomial profile): if `Π_k ∼ C k^α` with `C, α > 0`, then
`k(i) ∼ (i/C)^{1/α}`, and `H_seq(pᵢ) = k(i)`. The paper's extra hypothesis that `Π_k` is
eventually strictly increasing is dropped (`Π` is nondecreasing, which suffices).

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 4 (`integers-2026-A116-lem-4`). -/
public theorem_wanted seqHeightIndex_isEquivalent {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop (fun i : ℕ => (seqHeightIndex π i : ℝ))
        (fun i : ℕ => ((i : ℝ) / C) ^ (1 / α)) ∧
      ∀ i, 1 ≤ i → canonicalSeqHeight π (nthPrimeOne i) = seqHeightIndex π i

/-- Lemma 5 (a logarithmic-integral sum): for fixed `β > 0`,
`∑_{2 ≤ i ≤ m} i^{β-1} / log i ∼ m^β / (β log m)` as `m → ∞`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Lemma 5 (`integers-2026-A116-lem-5`). -/
public theorem_wanted sum_rpow_div_log_isEquivalent {β : ℝ} (hβ : 0 < β) :
    Asymptotics.IsEquivalent atTop
      (fun m : ℕ => ∑ i ∈ Finset.Icc 2 m, (i : ℝ) ^ (β - 1) / Real.log i)
      (fun m : ℕ => (m : ℝ) ^ β / (β * Real.log m))

/-- Theorem 5 (prime-harmonic growth for the canonical sequential model): if `Π_k ∼ C k^α` with
`C, α > 0` and `m = π(x)`, then `S_seq(x) = ∑_{p ≤ x} H_seq(p)/p ∼ (α / C^{1/α}) m^{1/α} / log m`,
and `S_seq(x) ≍ x^{1/α} / (log x)^{1+1/α}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Theorem 5 (`integers-2026-A116-thm-5`). -/
public theorem_wanted canonicalSeq_primeHarmonicSum {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p)
        (fun x : ℝ => α / C ^ (1 / α) *
          ((Nat.primeCounting ⌊x⌋₊ : ℝ) ^ (1 / α) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / α) / Real.log x ^ (1 + 1 / α))

/-- Corollary 2 (average-order scale from Equation (7)): if `Π_k ∼ C k^α` with `C, α > 0`, then
the leading prime-sum term `x S_seq(x) = x ∑_{p ≤ x} H_seq(p)/p`, the error term
`∑_{p ≤ x} H_seq(p) log x / log p` of Equation (7), and `F_seq(x) = ∑_{n ≤ x} H_seq(n)` are all
`≍ x^{1+1/α} / (log x)^{1+1/α}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 2 (`integers-2026-A116-cor-2`),
statement read from the journal PDF (the corpus record carries the prose of Section 7.6 that
follows it). -/
public theorem_wanted canonicalSeq_averageOrder {π : ℕ → ℕ} {C α : ℝ} (hC : 0 < C)
    (hα : 0 < α)
    (hcum : Asymptotics.IsEquivalent atTop (fun k : ℕ => (profilePartialSum π k : ℝ))
      (fun k : ℕ => C * (k : ℝ) ^ α)) :
    (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight π p : ℝ) * (Real.log x / Real.log p)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight π n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (1 + 1 / α) / Real.log x ^ (1 + 1 / α))

/-- Corollary 3 (ordinary partition profile `π_k = 1`, so `α = C = 1`): the canonical sequential
model has `S_seq(x) ≍ x / (log x)²` and `F_seq(x) = ∑_{n ≤ x} H_seq(n) ≍ x² / (log x)²`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 3 (`integers-2026-A116-cor-3`). -/
public theorem_wanted canonicalSeq_partitionProfile_growth :
    (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (canonicalSeqHeight (fun _ => 1) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x / Real.log x ^ 2) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun _ => 1) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ 2 / Real.log x ^ 2)

/-- Corollary 4 (plane partition profile `π_k = k`, so `Π_k = k(k+1)/2`, `α = 2`, `C = 1/2`):
`S_seq(x) ∼ 2√2 √π(x) / log π(x)`, `S_seq(x) ≍ x^{1/2} / (log x)^{3/2}`,
`F_seq(x) ≍ x S_seq(x)`, and `F_seq(x) ≍ x^{3/2} / (log x)^{3/2}`.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Corollary 4 (`integers-2026-A116-cor-4`). -/
public theorem_wanted canonicalSeq_planePartitionProfile_growth :
    Asymptotics.IsEquivalent atTop
        (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p)
        (fun x : ℝ => 2 * Real.sqrt 2 *
          (Real.sqrt (Nat.primeCounting ⌊x⌋₊) / Real.log (Nat.primeCounting ⌊x⌋₊))) ∧
      (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) =Θ[atTop]
        (fun x : ℝ => x ^ (1 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ)) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x * ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
          (canonicalSeqHeight (fun k => k) p : ℝ) / p) ∧
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (canonicalSeqHeight (fun k => k) n : ℝ)) =Θ[atTop]
        (fun x : ℝ => x ^ (3 / 2 : ℝ) / Real.log x ^ (3 / 2 : ℝ))

end

end MetaMathlibExt
