/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.Algebra.Polynomial.PrimeValueConditions
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace MetaMathlibExt

@[expose] public section

/-- Ballot's Lemma 1: for an odd prime `p` and an integer discriminant `D ≡ 0` or `1 (mod 4)`
prime to `p`, every odd prime of the form `p' = p + D x` (`x ∈ ℤ`) has the same Kronecker
symbol `(D | p') = (D | p)`. For odd primes the symbol is the Jacobi (Legendre) symbol
`jacobiSym D p`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 1 (`integers-2026-A102-lem-1`). -/
public theorem_wanted jacobiSym_prime_add_mul_eq {p p' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp' : p'.Prime) (hp'2 : p' ≠ 2) {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hDp : IsCoprime D p) {x : ℤ} (hx : (p' : ℤ) = p + D * x) :
    jacobiSym D p' = jacobiSym D p

/-- Ballot's Lemma 2: let `ε₁, ε₂, ε₃ ∈ {±1}`, let `c₁, c₂, c₃` be positive pairwise coprime
integers, let `g ≠ 0`, and put `n = (c₁ g + ε₁)(c₂ g + ε₂)(c₃ g + ε₃)` and
`εₙ = ε₁ ε₂ ε₃`. Then `cᵢ g ∣ n - εₙ` for `i = 1, 2, 3` if and only if
`g (ε₃ c₁ c₂ + ε₂ c₁ c₃ + ε₁ c₂ c₃) + εₙ (ε₁ c₁ + ε₂ c₂ + ε₃ c₃) ≡ 0 (mod c₁ c₂ c₃)`
(the paper's congruence (9)).

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 2 (`integers-2026-A102-lem-2`). -/
public theorem_wanted mul_dvd_prod_sub_sign_iff {ε₁ ε₂ ε₃ c₁ c₂ c₃ g : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁₂ : IsCoprime c₁ c₂) (h₁₃ : IsCoprime c₁ c₃) (h₂₃ : IsCoprime c₂ c₃) (hg : g ≠ 0) :
    (c₁ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃ ∧
      c₂ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃ ∧
      c₃ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃) ↔
    c₁ * c₂ * c₃ ∣
      g * (ε₃ * c₁ * c₂ + ε₂ * c₁ * c₃ + ε₁ * c₂ * c₃) +
        ε₁ * ε₂ * ε₃ * (ε₁ * c₁ + ε₂ * c₂ + ε₃ * c₃)

/-! ## Absolute Lucas pseudoprimes -/

/-- Williams' absolute Lucas `D`-pseudoprime, called a `D`-Carmichael number in the paper: for
a discriminant `D ≡ 0, 1 (mod 4)` (the paper's standing assumption; for other `D` no Lucas
sequence has discriminant `D`, so the last clause would be vacuous), an odd composite integer
`n`, prime to `D`, such that `n ∣ U_{n - εₙ}(P, Q)` with `εₙ = (D | n)`
for every Lucas sequence `U(P, Q)` with coprime parameters, discriminant `P² - 4Q = D` and `Q`
prime to `n`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of absolute Lucas `D`-pseudoprimes, after [17]). -/
def IsDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  (D % 4 = 0 ∨ D % 4 = 1) ∧ Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ IsCoprime D n ∧
    ∀ params : LucasSequenceParams, params.IsCoprime → params.p ^ 2 - 4 * params.q = D →
      IsCoprime params.q n → (n : ℤ) ∣ lucasU params (n - jacobiSym D n).toNat

/-- A `D`-Carmichael number is composite.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1. -/
theorem IsDCarmichael.not_prime {D : ℤ} {n : ℕ} (h : IsDCarmichael D n) : ¬ n.Prime :=
  h.2.2.2.1

/-- `9` is not a `5`-Carmichael number: `(5 | 9) = 1` and the Fibonacci sequence
`U(1, -1)` has `F₈ = 21`, which `9` does not divide.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1. -/
theorem not_isDCarmichael_five_nine : ¬ IsDCarmichael 5 9 := by
  rintro ⟨-, -, -, -, -, h⟩
  have hc : fibonacciLucasParams.IsCoprime := ⟨1, 0, by simp [fibonacciLucasParams]⟩
  have hj : jacobiSym 5 9 = 1 := by norm_num
  have h9 := h fibonacciLucasParams hc (by simp [fibonacciLucasParams])
    (by simpa [fibonacciLucasParams] using (isCoprime_one_left (x := (9 : ℤ))).neg_left)
  rw [hj, lucasU_fibonacciLucasParams] at h9
  norm_num [Nat.fib_add_two] at h9

/-- The paper's extended digit function `s_p(n) = ∑ cᵢ εₚⁱ`, where `n = ∑ cᵢ pⁱ` is the base-`p`
expansion and `εₚ = (D | p)`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
equation (6). -/
def lucasDigitSum (D : ℤ) (p n : ℕ) : ℤ :=
  ((Nat.digits p n).mapIdx fun i c => (c : ℤ) * jacobiSym D p ^ i).sum

/-- The paper's example: `6601 = 5·7 + 7² + 5·7³ + 2·7⁴` and `(5 | 7) = -1`, so
`s₇(6601) = -5 + 1 - 5 + 2 = -7`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
equation (6) and the example `m = 6601`. -/
theorem lucasDigitSum_five_seven_6601 : lucasDigitSum 5 7 6601 = -7 := by
  have hj : jacobiSym 5 7 = -1 := by norm_num
  norm_num [lucasDigitSum, hj]

/-- A primary `D`-Carmichael number: a `D`-Carmichael number `n` whose degree is at most one,
i.e. for every prime `p ∣ n` the integer `dₚ` with `sₚ(n) = εₙ + dₚ (p - εₚ)` has `|dₚ| ≤ 1`,
stated as `|sₚ(n) - εₙ| ≤ p - εₚ`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
def IsPrimaryDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  IsDCarmichael D n ∧ ∀ p ∈ n.primeFactors,
    |lucasDigitSum D p n - jacobiSym D n| ≤ p - jacobiSym D p

/-- A secondary `D`-Carmichael number: a `D`-Carmichael number of degree exactly two, i.e.
`|dₚ| ≤ 2` for all primes `p ∣ n` and `|dₚ| > 1` for some.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
def IsSecondaryDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  IsDCarmichael D n ∧
    (∀ p ∈ n.primeFactors, |lucasDigitSum D p n - jacobiSym D n| ≤ 2 * (p - jacobiSym D p)) ∧
    ∃ p ∈ n.primeFactors, p - jacobiSym D p < |lucasDigitSum D p n - jacobiSym D n|

/-- A primary `D`-Carmichael number is `D`-Carmichael.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
theorem IsPrimaryDCarmichael.isDCarmichael {D : ℤ} {n : ℕ} (h : IsPrimaryDCarmichael D n) :
    IsDCarmichael D n :=
  h.1

/-- A `σ`-Carmichael number for a signature `σ = (ε₁, …, εᵣ)` of signs (`r ≥ 2`, as signatures
are defined in the paper): an odd squarefree `n = p₁ ⋯ pᵣ`, `p₁ < ⋯ < pᵣ`, that is
`D`-Carmichael for every discriminant `D ≡ 0, 1 (mod 4)`
with `(D | pᵢ) = εᵢ` for all `i`. `Nat.primeFactorsList` lists the `pᵢ` in increasing order.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 4. -/
def IsSignatureCarmichael (σ : List ℤ) (n : ℕ) : Prop :=
  Squarefree n ∧ Odd n ∧ 2 ≤ σ.length ∧ n.primeFactorsList.length = σ.length ∧
    (∀ e ∈ σ, e = 1 ∨ e = -1) ∧
    ∀ D : ℤ, (D % 4 = 0 ∨ D % 4 = 1) →
      n.primeFactorsList.map (fun p => jacobiSym D p) = σ → IsDCarmichael D n

/-- `4` is not `σ`-Carmichael for any signature: it is not squarefree.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 4. -/
theorem not_isSignatureCarmichael_four (σ : List ℤ) : ¬ IsSignatureCarmichael σ 4 := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- A universal `D`-form with respect to a signature `σ`, for products of linear factors
`aᵢ x + bᵢ` (all forms in the paper are of this shape): every factor is irreducible
(`aᵢ ≠ 0`, `gcd(aᵢ, bᵢ) = 1`), the product is not identically zero modulo any prime, and
whenever all factors take (positive) prime values at some integer `x`, their product is a
`D`-Carmichael number with signature `σ`. The paper says "for some `n ≥ 0`"; integer `x` is
used because its forms `p + D x` (Theorem 4) and Chernick forms (Theorem 5) allow `D < 0`,
where `x ≥ 0` would leave only finitely many positive values.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of a universal `D`-form). -/
def IsUniversalLinearDForm (D : ℤ) (σ : List ℤ) (l : List (ℤ × ℤ)) : Prop :=
  (∀ ab ∈ l, ab.1 ≠ 0 ∧ Int.gcd ab.1 ab.2 = 1) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * (x : ℤ) + ab.2).prod) ∧
    ∀ x : ℤ, (∀ ab ∈ l, 0 < ab.1 * x + ab.2 ∧ (ab.1 * x + ab.2).natAbs.Prime) →
      IsDCarmichael D (l.map fun ab => (ab.1 * x + ab.2).natAbs).prod ∧
        ((l.map fun ab => (ab.1 * x + ab.2).natAbs).prod.primeFactorsList.map
          fun p => jacobiSym D p) = σ

/-- `x (x + 1)` is not a universal form for any `D` and `σ`: it is always even.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of a universal `D`-form). -/
theorem not_isUniversalLinearDForm_mul_succ (D : ℤ) (σ : List ℤ) :
    ¬ IsUniversalLinearDForm D σ [(1, 0), (1, 1)] := by
  rintro ⟨-, h, -⟩
  obtain ⟨x, hx⟩ := h 2 Nat.prime_two
  apply hx
  simpa [mul_comm] using (Int.even_mul_succ_self x).two_dvd

/-! ## Results -/

/-- Williams' criterion: for `D ≡ 0, 1 (mod 4)` and an odd composite `n` prime to `D`, `n` is
`D`-Carmichael iff `n` is squarefree and `p - εₚ ∣ n - εₙ` for every prime `p ∣ n`. The record
states it for every odd positive `n`; primes (and `1`) satisfy the criterion but are not
`D`-Carmichael, so `n` is taken composite and prime to `D` as in the definition.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 1 (`integers-2026-A102-thm-1`). -/
public theorem_wanted isDCarmichael_iff_korselt {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {n : ℕ}
    (hodd : Odd n) (hn : 1 < n) (hnp : ¬ n.Prime) (hDn : IsCoprime D n) :
    IsDCarmichael D n ↔
      Squarefree n ∧ ∀ p ∈ n.primeFactors, ((p : ℤ) - jacobiSym D p) ∣ ((n : ℤ) - jacobiSym D n)

/-- Wagstaff: the prime `k`-tuples conjecture implies there are infinitely many primary
Carmichael numbers with three prime factors (Carmichael: composite with `aⁿ⁻¹ ≡ 1 (mod n)` for
all `a` prime to `n`; primary: the base-`p` digit sum of `n` is `p` for every prime `p ∣ n`).
The prime `k`-tuples conjecture (the paper's Conjecture 1) is the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 2 (`integers-2026-A102-thm-2`). -/
public theorem_wanted infinite_primary_carmichael_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p}.Infinite

/-- Korselt criterion for `σ`-Carmichael numbers: for a signature `σ = (ε₁, …, εᵣ)` of length
`r ≥ 2` and an odd positive `n`, `n` is `σ`-Carmichael iff `n` is squarefree with exactly `r`
prime factors `p₁ < ⋯ < pᵣ` and `pᵢ - εᵢ ∣ n - ε_σ` for all `i`, where `ε_σ = ∏ εᵢ`. The
length condition `r ≥ 2` comes from the paper's definition of signatures; the record leaves
the matching of `εₚ` to `p` implicit, here `p = pᵢ` pairs with `εᵢ`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 3 (`integers-2026-A102-thm-3`). -/
public theorem_wanted isSignatureCarmichael_iff {σ : List ℤ} (hσ : ∀ e ∈ σ, e = 1 ∨ e = -1)
    (hlen : 2 ≤ σ.length) {n : ℕ} (hodd : Odd n) :
    IsSignatureCarmichael σ n ↔
      Squarefree n ∧ n.primeFactorsList.length = σ.length ∧
        ∀ pe ∈ n.primeFactorsList.zip σ, ((pe.1 : ℤ) - pe.2) ∣ ((n : ℤ) - σ.prod)

/-- Two-prime-factor `D`-Carmichael numbers: if `p < q` are primes with `pq` `D`-Carmichael
(`D ≡ 0, 1 (mod 4)`), then `q = p + 2`, `(p + Dx)(q + Dx)` is a universal `D`-form of
signature `(-1, 1)` whose prime-factor values are primary `D`-Carmichael numbers, and the prime
`k`-tuples conjecture gives infinitely many primary `D`-Carmichael numbers of signature
`(-1, 1)`. Moreover the two-prime-factor `5`-Carmichael numbers are exactly the products
`(10x + 7)(10x + 9)` with `x ≥ 1` and both factors prime. The prime `k`-tuples conjecture (the
paper's Conjecture 1) is the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 4 (`integers-2026-A102-thm-4`). -/
public theorem_wanted twoFactor_isDCarmichael {D : ℤ}
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ p q : ℕ, p.Prime → q.Prime → p < q → IsDCarmichael D (p * q) →
      IsUniversalLinearDForm D [-1, 1] [(D, p), (D, q)] ∧ q = p + 2 ∧
        (∀ x : ℤ, 0 < (p : ℤ) + D * x → ((p : ℤ) + D * x).natAbs.Prime →
          0 < (q : ℤ) + D * x → ((q : ℤ) + D * x).natAbs.Prime →
          IsPrimaryDCarmichael D (((p : ℤ) + D * x) * ((q : ℤ) + D * x)).natAbs) ∧
        {n : ℕ | IsPrimaryDCarmichael D n ∧
          n.primeFactorsList.map (fun r => jacobiSym D r) = [-1, 1]}.Infinite) ∧
    ∀ n : ℕ, (IsDCarmichael 5 n ∧ n.primeFactorsList.length = 2) ↔
      ∃ x : ℕ, 1 ≤ x ∧ (10 * x + 7).Prime ∧ (10 * x + 9).Prime ∧ n = (10 * x + 7) * (10 * x + 9)

/-- Chernick-type universal forms for three-prime-factor `D`-Carmichael numbers: let
`3 < p₁ < p₂ < p₃` be primes with `p₁p₂p₃` `D`-Carmichael of signature `σ = (ε₁, ε₂, ε₃)`, let
`g = gcd(pᵢ - εᵢ)` and `g cᵢ = pᵢ - εᵢ` with the `cᵢ` pairwise coprime. Then
`(D c₁² c₂ c₃ x + p₁)(D c₁ c₂² c₃ x + p₂)(D c₁ c₂ c₃² x + p₃)` is a universal `D`-form with
respect to `σ`. `D ≡ 0, 1 (mod 4)` (the paper's standing assumption) is part of `IsDCarmichael`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 5 (`integers-2026-A102-thm-5`). -/
public theorem_wanted isUniversalLinearDForm_chernick {D : ℤ} {p₁ p₂ p₃ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime) (h3 : 3 < p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) (hC : IsDCarmichael D (p₁ * p₂ * p₃))
    {g c₁ c₂ c₃ : ℤ}
    (hg : g = Int.gcd (Int.gcd (p₁ - jacobiSym D p₁) (p₂ - jacobiSym D p₂))
      (p₃ - jacobiSym D p₃))
    (hc₁ : g * c₁ = p₁ - jacobiSym D p₁) (hc₂ : g * c₂ = p₂ - jacobiSym D p₂)
    (hc₃ : g * c₃ = p₃ - jacobiSym D p₃)
    (hc₁₂ : IsCoprime c₁ c₂) (hc₁₃ : IsCoprime c₁ c₃) (hc₂₃ : IsCoprime c₂ c₃) :
    IsUniversalLinearDForm D [jacobiSym D p₁, jacobiSym D p₂, jacobiSym D p₃]
      [(D * c₁ ^ 2 * c₂ * c₃, p₁), (D * c₁ * c₂ ^ 2 * c₃, p₂), (D * c₁ * c₂ * c₃ ^ 2, p₃)]

/-- The prime `k`-tuples conjecture implies that for every signature `σ` of length three there
are infinitely many primary `5`-Carmichael numbers of signature `σ`. The prime `k`-tuples
conjecture (the paper's Conjecture 1) is the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 6 (`integers-2026-A102-thm-6`). -/
public theorem_wanted infinite_primary_fiveCarmichael_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite)
    (σ : List ℤ) (hσ : ∀ e ∈ σ, e = 1 ∨ e = -1) (hlen : σ.length = 3) :
    {n : ℕ | IsPrimaryDCarmichael 5 n ∧
      n.primeFactorsList.map (fun p => jacobiSym 5 p) = σ}.Infinite

/-- `105, 195, 255, 399, 561, 2703` are the only numbers `3qr` (`3 < q < r` primes) that are
`D`-Carmichael for some discriminant `D ≡ 0, 1 (mod 4)`, and each is so for only one
signature: any two such `D`, `D'` give the same signs at `3`, `q` and `r`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 7 (`integers-2026-A102-thm-7`). -/
public theorem_wanted threeQR_isDCarmichael_iff {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (h3q : 3 < q) (hqr : q < r) :
    ((∃ D : ℤ, IsDCarmichael D (3 * q * r)) ↔
      3 * q * r ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ)) ∧
    ∀ D D' : ℤ, IsDCarmichael D (3 * q * r) → IsDCarmichael D' (3 * q * r) →
      jacobiSym D 3 = jacobiSym D' 3 ∧ jacobiSym D q = jacobiSym D' q ∧
        jacobiSym D r = jacobiSym D' r

/-- The prime `k`-tuples conjecture implies infinitely many `x ≥ 0` with `p = 30x + 17`, `q = 30x
+ 19`, `r = 180x + 107`, `s = 180x + 109` all prime; for every such `x`, `m = pqr` and `n = pqs`
are primary `5`-Carmichael numbers and `N = pqrs` is a secondary `5`-Carmichael number. The prime
`k`-tuples conjecture (the paper's Conjecture 1) is the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 8 (`integers-2026-A102-thm-8`). -/
public theorem_wanted primaryFiveCarmichael_pairs_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ x : ℕ, (30 * x + 17).Prime → (30 * x + 19).Prime → (180 * x + 107).Prime →
      (180 * x + 109).Prime →
      IsPrimaryDCarmichael 5 ((30 * x + 17) * (30 * x + 19) * (180 * x + 107)) ∧
      IsPrimaryDCarmichael 5 ((30 * x + 17) * (30 * x + 19) * (180 * x + 109)) ∧
      IsSecondaryDCarmichael 5
        ((30 * x + 17) * (30 * x + 19) * (180 * x + 107) * (180 * x + 109))) ∧
    {x : ℕ | (30 * x + 17).Prime ∧ (30 * x + 19).Prime ∧ (180 * x + 107).Prime ∧
      (180 * x + 109).Prime}.Infinite

/-- The prime `k`-tuples conjecture implies infinitely many `x ≥ 0` with `p = 78x + 137`, `q = 78x
+ 139`, `r = 468x + 827`, `s = 468x + 829` all prime; for every such `x`, `m = pqr` and `n = pqs`
are primary `13`-Carmichael numbers of signatures `- + -` and `- + +`, and `N = pqrs` is a
secondary `13`-Carmichael number. The prime `k`-tuples conjecture (the paper's Conjecture 1) is
the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 9 (`integers-2026-A102-thm-9`). -/
public theorem_wanted primaryThirteenCarmichael_pairs_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ x : ℕ, (78 * x + 137).Prime → (78 * x + 139).Prime → (468 * x + 827).Prime →
      (468 * x + 829).Prime →
      IsPrimaryDCarmichael 13 ((78 * x + 137) * (78 * x + 139) * (468 * x + 827)) ∧
      IsPrimaryDCarmichael 13 ((78 * x + 137) * (78 * x + 139) * (468 * x + 829)) ∧
      (((78 * x + 137) * (78 * x + 139) * (468 * x + 827)).primeFactorsList.map
        fun p => jacobiSym 13 p) = [-1, 1, -1] ∧
      (((78 * x + 137) * (78 * x + 139) * (468 * x + 829)).primeFactorsList.map
        fun p => jacobiSym 13 p) = [-1, 1, 1] ∧
      IsSecondaryDCarmichael 13
        ((78 * x + 137) * (78 * x + 139) * (468 * x + 827) * (468 * x + 829))) ∧
    {x : ℕ | (78 * x + 137).Prime ∧ (78 * x + 139).Prime ∧ (468 * x + 827).Prime ∧
      (468 * x + 829).Prime}.Infinite

/-- The forms `(390z + 137)(390z + 139)(2340z + 827)` and `(390z + 137)(390z + 139)(2340z + 829)`
are universal `5`- and `13`-forms with respective signatures `- + -` and `- + +`, yielding only
primary `5`- and `13`-Carmichael numbers; the four-factor form with both last factors is a
universal `5`- and `13`-form of signature `- + - +` yielding secondary `5`- and `13`-Carmichael
numbers; and the prime `k`-tuples conjecture gives infinitely many `z` with all four factors
prime. The paper (and the record) print "universal 7- and 13-forms"; `7 ≢ 0, 1 (mod 4)` is not
a discriminant, and the next sentence and the proof (combining the `5`-form of Theorem 8 with
the `13`-form of Theorem 9) fix it as `5`. The prime `k`-tuples conjecture (the paper's Conjecture
1) is the hypothesis `hk`: for linear
forms `aᵢ x + bᵢ` with `aᵢ ≥ 1` whose product has no fixed prime divisor, infinitely many `x`
make every form a (positive) prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 10 (`integers-2026-A102-thm-10`). -/
public theorem_wanted universal_fiveThirteen_forms
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ D ∈ ({5, 13} : Finset ℤ),
      IsUniversalLinearDForm D [-1, 1, -1] [(390, 137), (390, 139), (2340, 827)] ∧
      IsUniversalLinearDForm D [-1, 1, 1] [(390, 137), (390, 139), (2340, 829)] ∧
      IsUniversalLinearDForm D [-1, 1, -1, 1]
        [(390, 137), (390, 139), (2340, 827), (2340, 829)] ∧
      ∀ z : ℕ, (390 * z + 137).Prime → (390 * z + 139).Prime →
        ((2340 * z + 827).Prime →
          IsPrimaryDCarmichael D ((390 * z + 137) * (390 * z + 139) * (2340 * z + 827))) ∧
        ((2340 * z + 829).Prime →
          IsPrimaryDCarmichael D ((390 * z + 137) * (390 * z + 139) * (2340 * z + 829))) ∧
        ((2340 * z + 827).Prime → (2340 * z + 829).Prime →
          IsSecondaryDCarmichael D
            ((390 * z + 137) * (390 * z + 139) * (2340 * z + 827) * (2340 * z + 829)))) ∧
    {z : ℕ | (390 * z + 137).Prime ∧ (390 * z + 139).Prime ∧ (2340 * z + 827).Prime ∧
      (2340 * z + 829).Prime}.Infinite

/-- Schinzel's H-hypothesis implies infinitely many numbers are simultaneously primary
`5`-Carmichael of signature `+ - -` and primary `(-11)`-Carmichael of signature `- + -`. The
H-hypothesis (the paper's Conjecture 2) is the hypothesis `hH`, phrased with the canonical
`Polynomial.BunyakovskyCondition` and `Polynomial.SchinzelCondition`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 11 (`integers-2026-A102-thm-11`). -/
public theorem_wanted infinite_primary_five_negEleven_of_schinzelH
    (hH : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, Polynomial.BunyakovskyCondition f) →
      Polynomial.SchinzelCondition fs →
      {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}.Infinite) :
    {n : ℕ | IsPrimaryDCarmichael 5 n ∧
      n.primeFactorsList.map (fun p => jacobiSym 5 p) = [1, -1, -1] ∧
      IsPrimaryDCarmichael (-11) n ∧
      n.primeFactorsList.map (fun p => jacobiSym (-11) p) = [-1, 1, -1]}.Infinite

/-- If `n` is `D`-Carmichael and `D'`-Carmichael for two signatures of opposite signs
(`(D | n) ≠ (D' | n)`), then the signatures have opposite entries (`(D' | p) = -(D | p)` for
every prime `p ∣ n`), `ω(n)` is odd and `3 ∤ n`. The paper's `n ∈ C(σ) ∩ C(σ')` is read as `n`
being `D`-Carmichael with signature `σ` and `D'`-Carmichael with signature `σ'`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 12 (`integers-2026-A102-thm-12`). -/
public theorem_wanted isDCarmichael_opposite_signs {D D' : ℤ} {n : ℕ} (h : IsDCarmichael D n)
    (h' : IsDCarmichael D' n)
    (hs : jacobiSym D n ≠ jacobiSym D' n) :
    (∀ p ∈ n.primeFactors, jacobiSym D' p = -jacobiSym D p) ∧ Odd n.primeFactors.card ∧
      ¬ 3 ∣ n

/-- There are no three-prime-factor numbers that are bi-Carmichael with respect to two signatures
of opposite signs: if `n` has three prime factors and is `D`- and `D'`-Carmichael, then
`(D | n) = (D' | n)`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 13 (`integers-2026-A102-thm-13`). -/
public theorem_wanted jacobiSym_eq_of_isDCarmichael_three {D D' : ℤ} {n : ℕ}
    (h3 : n.primeFactors.card = 3) (h : IsDCarmichael D n) (h' : IsDCarmichael D' n) :
    jacobiSym D n = jacobiSym D' n

/-- Ballot's Lemma 3: with `εᵢ`, `cᵢ`, `g`, `n = (c₁g + ε₁)(c₂g + ε₂)(c₃g + ε₃)` as in Lemma 2
and `cᵢ g ∣ n - εₙ` for `i = 1, 2, 3`, every nonzero `h ≡ g (mod c₁c₂c₃)` gives
`cᵢ h ∣ m - εₙ` for `m = (c₁h + ε₁)(c₂h + ε₂)(c₃h + ε₃)`. The record omits the divisibility
hypothesis on `g`, without which the claim fails (`c = (1, 2, 3)`, `ε = (1, 1, 1)`, `g = h = 1`:
`2 ∤ 24 - 1`); the paper's proof ("replace
`g` by `h` in (9)") uses it.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 3 (`integers-2026-A102-lem-3`). -/
public theorem_wanted mul_dvd_prod_sub_sign_of_modEq {ε₁ ε₂ ε₃ c₁ c₂ c₃ g h : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁₂ : IsCoprime c₁ c₂) (h₁₃ : IsCoprime c₁ c₃) (h₂₃ : IsCoprime c₂ c₃) (hg : g ≠ 0)
    (hgdvd : ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃)
    (hh : h ≠ 0) (hhg : h ≡ g [ZMOD c₁ * c₂ * c₃]) :
    ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * h ∣ (c₁ * h + ε₁) * (c₂ * h + ε₂) * (c₃ * h + ε₃) - ε₁ * ε₂ * ε₃

/-- If `3qr` (`3 < q < r` primes) is `D`-Carmichael of signature `(α, β, γ)` (`D ≡ 0, 1 (mod 4)`),
then `q - β ∣ 3r - αγ` and `r - γ ∣ 3q - αβ`; moreover `r = 3q + 2γ` if `γ = -αβ`, and
`2r = 3q + γ` if `γ = αβ`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 4 (`integers-2026-A102-lem-4`). -/
public theorem_wanted threeQR_isDCarmichael_divisibility {D : ℤ} {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (h3q : 3 < q) (hqr : q < r)
    (h : IsDCarmichael D (3 * q * r)) :
    ((q : ℤ) - jacobiSym D q) ∣ (3 * r - jacobiSym D 3 * jacobiSym D r) ∧
    ((r : ℤ) - jacobiSym D r) ∣ (3 * q - jacobiSym D 3 * jacobiSym D q) ∧
    (jacobiSym D r = -(jacobiSym D 3 * jacobiSym D q) → (r : ℤ) = 3 * q + 2 * jacobiSym D r) ∧
    (jacobiSym D r = jacobiSym D 3 * jacobiSym D q → 2 * (r : ℤ) = 3 * q + jacobiSym D r)

/-- Williams: for `D ≡ 0, 1 (mod 4)` and primes `p₁ < p₂`, the product `p₁p₂` is `D`-Carmichael
iff `p₂ = p₁ + 2`, `(D | p₁) = -1` and `(D | p₂) = 1`.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Proposition 1 (`integers-2026-A102-prop-1`). -/
public theorem_wanted isDCarmichael_mul_iff {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {p₁ p₂ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h12 : p₁ < p₂) :
    IsDCarmichael D (p₁ * p₂) ↔ p₂ = p₁ + 2 ∧ jacobiSym D p₁ = -1 ∧ jacobiSym D p₂ = 1

end

end MetaMathlibExt
