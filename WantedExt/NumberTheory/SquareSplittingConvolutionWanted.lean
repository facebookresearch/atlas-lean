/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

@[expose] public section

open Filter Topology Asymptotics

/-- The squarefree part `u(n)` in the decomposition `n = u(n) v(n)²` with
`u(n)` squarefree: the product of the primes dividing `n` to an odd power.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2
(`n = u(n) v(n)²`, Theorems 2 and 3). -/
public def squareSplitU (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => p ^ (e % 2)

/-- The square root `v(n)` of the square part in `n = u(n) v(n)²`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public def squareSplitV (n : ℕ) : ℕ :=
  n.factorization.prod fun p e => p ^ (e / 2)

/-- `u(1) = 1`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitU_one : squareSplitU 1 = 1 := by
  simp [squareSplitU]

/-- `v(1) = 1`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitV_one : squareSplitV 1 = 1 := by
  simp [squareSplitV]

/-- The decomposition `n = u(n) v(n)²` for `n ≠ 0`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitU_mul_squareSplitV_sq {n : ℕ} (hn : n ≠ 0) :
    squareSplitU n * squareSplitV n ^ 2 = n := by
  unfold squareSplitU squareSplitV
  rw [Finsupp.prod, Finsupp.prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The divisor system `A(n) = {u₁ v₁² : u₁ ∣ u(n), v₁ ∣ v(n)}`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1. -/
public def squareSplitDivisors (n : ℕ) : Finset ℕ :=
  ((squareSplitU n).divisors ×ˢ (squareSplitV n).divisors).image fun x => x.1 * x.2 ^ 2

/-- `A(1) = {1}`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1. -/
public theorem squareSplitDivisors_one : squareSplitDivisors 1 = {1} := by
  simp [squareSplitDivisors, squareSplitU_one, squareSplitV_one]

/-- The square-splitting `A`-convolution of Narkiewicz type,
`(f ⋆ g)(n) = ∑_{d ∈ A(n)} f(d) g(n/d)` for `n ≥ 1` (and `0` at `0`, as for
every `ArithmeticFunction`).

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2
and Theorem 4 (`F = 1 ⋆ f` means `F(n) = ∑_{d ∈ A(n)} f(d)`). -/
public noncomputable def squareSplitConv (f g : ArithmeticFunction ℂ) :
    ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else ∑ d ∈ squareSplitDivisors n, f d * g (n / d), by simp⟩

/-- Unfolding `f ⋆ g` at `n ≠ 0`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Section 2. -/
public theorem squareSplitConv_apply (f g : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    squareSplitConv f g n = ∑ d ∈ squareSplitDivisors n, f d * g (n / d) := by
  simp [squareSplitConv, hn]

/-- Corollary 1: if `f` and `g` are multiplicative, so is `f ⋆ g`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Corollary 1
(`integers-2026-A56-cor-1`). -/
public theorem_wanted squareSplitConv_isMultiplicative {f g : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) :
    (squareSplitConv f g).IsMultiplicative

/-- Theorem 1: `A(n)` is a divisor system (`1, n ∈ A(n)` and every element
divides `n`), `A` is multiplicative in the strong sense
(`A(mn) = A(m) A(n)` for coprime `m, n`), and
`τ⋆(n) = |A(n)| = d(u(n)) d(v(n)) = 2^{ω(u(n))} d(v(n))`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 1
(`integers-2026-A56-thm-1`). -/
public theorem_wanted squareSplitDivisors_properties :
    (∀ n ≠ 0, 1 ∈ squareSplitDivisors n ∧ n ∈ squareSplitDivisors n ∧
      ∀ d ∈ squareSplitDivisors n, d ∣ n) ∧
    (∀ m n, Nat.Coprime m n → squareSplitDivisors (m * n) =
      (squareSplitDivisors m ×ˢ squareSplitDivisors n).image fun x => x.1 * x.2) ∧
    (∀ n ≠ 0, (squareSplitDivisors n).card =
        (squareSplitU n).divisors.card * (squareSplitV n).divisors.card ∧
      (squareSplitDivisors n).card =
        2 ^ ArithmeticFunction.cardDistinctFactors (squareSplitU n) *
          (squareSplitV n).divisors.card)

/-- Theorem 2, ring part: `⋆` is commutative, associative, distributes over
`+`, and has identity `ε` (the arithmetic function `1`), so arithmetic
functions form a commutative ring under `+` and `⋆`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_commRing_axioms (f g h : ArithmeticFunction ℂ) :
    squareSplitConv f g = squareSplitConv g f ∧
      squareSplitConv (squareSplitConv f g) h = squareSplitConv f (squareSplitConv g h) ∧
      squareSplitConv f (g + h) = squareSplitConv f g + squareSplitConv f h ∧
      squareSplitConv 1 f = f

/-- Theorem 2, isomorphism part: `T f (u, v) = f(u v²)` (`u` squarefree,
`v ≥ 1`) is a bijection from arithmetic functions onto functions on
`{(u, v) : u squarefree, v ≥ 1}` (with `u ≥ 1` implied by squarefreeness), it
turns `⋆` into the bivariate Dirichlet convolution
`(F ⊙ G)(u, v) = ∑_{u₁ ∣ u} ∑_{v₁ ∣ v} F(u₁, v₁) G(u/u₁, v/v₁)`, and it is
additive (immediate).

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 2
(`integers-2026-A56-thm-2`). -/
public theorem_wanted squareSplitConv_bivariate_iso :
    (∀ (f g : ArithmeticFunction ℂ) (u v : ℕ), Squarefree u → 0 < v →
      squareSplitConv f g (u * v ^ 2) =
        ∑ u₁ ∈ u.divisors, ∑ v₁ ∈ v.divisors,
          f (u₁ * v₁ ^ 2) * g ((u / u₁) * (v / v₁) ^ 2)) ∧
    ∀ F : ℕ → ℕ → ℂ, ∃! f : ArithmeticFunction ℂ,
      ∀ u v, Squarefree u → 0 < v → f (u * v ^ 2) = F u v

/-- Theorem 3: the `⋆`-inverse `μ⋆` of the constant function `1` satisfies
`μ⋆(n) = μ(u(n)) μ(v(n))`; on prime powers `μ⋆(p) = μ⋆(p²) = -1`,
`μ⋆(p³) = 1`, `μ⋆(p^k) = 0` for `k ≥ 4`; and for `Re s > 1`,
`∑ μ⋆(n)/n^s = ∏_p (1 - p^{-s} - p^{-2s} + p^{-3s}) = 1/(ζ(s) ζ(2s))`.
`μ⋆` enters as any `m` with `1 ⋆ m = ε` (Theorem 4's inversion relation).

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 3
(`integers-2026-A56-thm-3`). -/
public theorem_wanted squareSplitMoebius_formula (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n = (ArithmeticFunction.moebius (squareSplitU n) : ℂ) *
      ArithmeticFunction.moebius (squareSplitV n)) ∧
    (∀ p : ℕ, p.Prime → m p = -1 ∧ m (p ^ 2) = -1 ∧ m (p ^ 3) = 1 ∧
      ∀ k, 4 ≤ k → m (p ^ k) = 0) ∧
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => m n) s = ∏' p : Nat.Primes,
        (1 - ((p : ℕ) : ℂ) ^ (-s) - ((p : ℕ) : ℂ) ^ (-(2 * s)) + ((p : ℕ) : ℂ) ^ (-(3 * s))) ∧
      LSeries (fun n => m n) s = 1 / (riemannZeta s * riemannZeta (2 * s))

/-- Theorem 4 (Möbius inversion): `F = 1 ⋆ f` if and only if `f = μ⋆ ⋆ F`,
i.e. `F(n) = ∑_{d ∈ A(n)} f(d)` for all `n` iff
`f(n) = ∑_{d ∈ A(n)} μ⋆(d) F(n/d)` for all `n`; `μ⋆` enters as any `m` with
`1 ⋆ m = ε`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 4
(`integers-2026-A56-thm-4`). -/
public theorem_wanted squareSplit_moebius_inversion (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    (f F : ArithmeticFunction ℂ) :
    F = squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) f ↔
      f = squareSplitConv m F

/-- Theorem 5: a multiplicative `f` has a unique `⋆`-inverse `g`, which is
multiplicative and satisfies on prime powers
`∑_{j ≤ ⌊k/2⌋} f(p^{2j}) g(p^{k-2j}) + 1_{k odd} ∑_{j ≤ ⌊k/2⌋} f(p^{2j+1}) g(p^{k-2j-1}) = ε(p^k)`,
with `g(1) = 1/f(1)`, `g(p) = -f(p)/f(1)²`, `g(p²) = -f(p²)/f(1)²`,
`g(p³) = (2 f(p) f(p²) - f(p³) f(1))/f(1)³`. The paper's hypothesis
`f(1) ≠ 0` is part of Mathlib's `IsMultiplicative` (`f 1 = 1`).

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 5
(`integers-2026-A56-thm-5`). -/
public theorem_wanted squareSplitConv_inverse_of_isMultiplicative {f : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) :
    ∃ g : ArithmeticFunction ℂ, squareSplitConv f g = 1 ∧
      (∀ g' : ArithmeticFunction ℂ, squareSplitConv f g' = 1 → g' = g) ∧
      g.IsMultiplicative ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        ∑ j ∈ Finset.range (k / 2 + 1), f (p ^ (2 * j)) * g (p ^ (k - 2 * j)) +
          (if Odd k then ∑ j ∈ Finset.range (k / 2 + 1),
            f (p ^ (2 * j + 1)) * g (p ^ (k - (2 * j + 1))) else 0) = 0) ∧
      g 1 = 1 / f 1 ∧
      ∀ p : ℕ, p.Prime →
        g p = -f p / f 1 ^ 2 ∧ g (p ^ 2) = -f (p ^ 2) / f 1 ^ 2 ∧
        g (p ^ 3) = (2 * f p * f (p ^ 2) - f (p ^ 3) * f 1) / f 1 ^ 3

/-- Theorem 7: the Euler-type function `φ⋆`, defined by
`∑_{d ∈ A(n)} φ⋆(d) = n` for all `n ≥ 1` (Theorem 8), is multiplicative with
`φ⋆(1) = 1`, `φ⋆(p) = p - 1`, and for `b ≥ 1`,
`φ⋆(p^{2b}) = (p² - 1) p^{2b-2}`, `φ⋆(p^{2b+1}) = (p - 1)(p² - 1) p^{2b-2}`;
equivalently `φ⋆(n) = φ(u(n)) v(n)² ∏_{p ∣ v(n)} (1 - 1/p²)`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 7
(`integers-2026-A56-thm-7`). -/
public theorem_wanted squareSplitTotient_formula (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    φ.IsMultiplicative ∧ φ 1 = 1 ∧
    (∀ p : ℕ, p.Prime → φ p = (p : ℤ) - 1 ∧
      ∀ b, 1 ≤ b → φ (p ^ (2 * b)) = ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2) ∧
        φ (p ^ (2 * b + 1)) = ((p : ℤ) - 1) * ((p : ℤ) ^ 2 - 1) * (p : ℤ) ^ (2 * b - 2)) ∧
    ∀ n ≠ 0, (φ n : ℚ) = (squareSplitU n).totient * (squareSplitV n : ℚ) ^ 2 *
      ∏ p ∈ (squareSplitV n).primeFactors, (1 - 1 / (p : ℚ) ^ 2)

/-- Theorem 8: for `φ⋆` defined by `∑_{d ∈ A(n)} φ⋆(d) = n`, the product
`M = ∏_p (1 - 1/p² + (p-1)²/p⁵)` converges absolutely, and for every
`ε ∈ (0, 1/2)`, `∑_{n ≤ x} φ⋆(n) = (M/2) x² + O_ε(x^{1+ε})`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 8
(`integers-2026-A56-thm-8`). -/
public theorem_wanted squareSplitTotient_sum_asymptotic (φ : ArithmeticFunction ℤ)
    (hφ : ∀ n ≠ 0, ∑ d ∈ squareSplitDivisors n, φ d = n) :
    Summable (fun p : Nat.Primes =>
      |-(1 / ((p : ℕ) : ℝ) ^ 2) + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5|) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (φ n : ℝ) -
        (∏' p : Nat.Primes,
          (1 - 1 / ((p : ℕ) : ℝ) ^ 2 + (((p : ℕ) : ℝ) - 1) ^ 2 / ((p : ℕ) : ℝ) ^ 5)) / 2 * x ^ 2)
        =O[atTop] fun x => x ^ (1 + ε)

/-- Theorem 9: for `Re s > 1`, with `τ⋆(n) = |A(n)|`,
`∑ τ⋆(n)/n^s = ∏_p ∑_k τ⋆(p^k)/p^{ks} = ∏_p (1 + 2p^{-s})/(1 - p^{-2s})²
= ζ(s)² ζ(2s)² H(s)`, where `H(s) = ∏_p (1 - 3p^{-2s} + 2p^{-3s})` converges
absolutely and is holomorphic for `Re s > 1/2`, and `H(1) ≠ 0`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 9
(`integers-2026-A56-thm-9`). -/
public theorem_wanted squareSplitDivisorCount_LSeries :
    let τ : ℕ → ℂ := fun n => ((squareSplitDivisors n).card : ℂ)
    let H : ℂ → ℂ := fun s => ∏' p : Nat.Primes,
      (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s)))
    (∀ s : ℂ, 1 < s.re →
      (∀ p : Nat.Primes, HasSum (fun k : ℕ => τ ((p : ℕ) ^ k) * ((p : ℕ) : ℂ) ^ (-(k * s)))
        ((1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2)) ∧
      LSeries (fun n => τ n) s = ∏' p : Nat.Primes,
        (1 + 2 * ((p : ℕ) : ℂ) ^ (-s)) / (1 - ((p : ℕ) : ℂ) ^ (-(2 * s))) ^ 2 ∧
      LSeries (fun n => τ n) s = riemannZeta s ^ 2 * riemannZeta (2 * s) ^ 2 * H s) ∧
    (∀ s : ℂ, 1 / 2 < s.re → Summable (fun p : Nat.Primes =>
      ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * s)) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * s))‖)) ∧
    DifferentiableOn ℂ H {s | 1 / 2 < s.re} ∧ H 1 ≠ 0

/-- Lemma 1: if `F(s) = ∑_{n ≥ 1} f(n) n^{-s} = ζ(s)² / ζ(2s) · G(s)`, where `G` is a
Dirichlet series absolutely convergent for `Re s > σ₀` with `σ₀ < 1/2`, then
`∑_{n ≤ x} f(n) = G(1)/ζ(2) x log x + G(1)/ζ(2) (2γ - 1 + G'(1)/G(1) - 2 ζ'(2)/ζ(2)) x
+ O(x^{1/2} (log x)³)`. `G` enters as the L-series of `g`; `F` is required to converge
absolutely for `Re s > 1` (so `LSeries f` is not its junk value), and `G(1) ≠ 0` is added
so that the printed quotient `G'(1)/G(1)` is meaningful.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Lemma 1
(`integers-2026-A56-lem-1`). -/
public theorem_wanted sum_asymptotic_of_LSeries_eq_zeta_sq_div_zeta_two_mul (f g : ℕ → ℂ)
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1 / 2) (hg : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable g s)
    (hf : ∀ s : ℂ, 1 < s.re →
      LSeriesSummable f s ∧ LSeries f s = riemannZeta s ^ 2 / riemannZeta (2 * s) * LSeries g s)
    (hG1 : LSeries g 1 ≠ 0) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n -
        (LSeries g 1 / riemannZeta 2 * x * Real.log x +
          LSeries g 1 / riemannZeta 2 * (2 * Real.eulerMascheroniConstant - 1 +
            deriv (LSeries g) 1 / LSeries g 1 - 2 * deriv riemannZeta 2 / riemannZeta 2) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- Theorem 10: with `τ⋆(n) = |A(n)|`, `A_τ = ∏_p (1 - 1/(p+1)²)` and
`B_τ = 6 ∑_p log p / ((p-1)(p+1)(p+2))`,
`∑_{n ≤ x} τ⋆(n) = A_τ x log x + A_τ (2γ - 1 - B_τ - 2 ζ'(2)/ζ(2)) x
+ O(x^{1/2} (log x)³)`. The extracted text is partly garbled; this reading is
the one consistent with Theorem 9 (`A_τ = ζ(2)² H(1)` and
`-B_τ - 2ζ'(2)/ζ(2) = 4ζ'(2)/ζ(2) + H'(1)/H(1)`), and is confirmed numerically.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 10
(`integers-2026-A56-thm-10`). -/
public theorem_wanted squareSplitDivisorCount_sum_asymptotic :
    let Aτ : ℝ := ∏' p : Nat.Primes, (1 - 1 / (((p : ℕ) : ℝ) + 1) ^ 2)
    let Bτ : ℝ := 6 * ∑' p : Nat.Primes, Real.log (p : ℕ) /
      ((((p : ℕ) : ℝ) - 1) * (((p : ℕ) : ℝ) + 1) * (((p : ℕ) : ℝ) + 2))
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((squareSplitDivisors n).card : ℝ) -
        (Aτ * x * Real.log x + Aτ * (2 * Real.eulerMascheroniConstant - 1 - Bτ -
          2 * (deriv riemannZeta 2 / riemannZeta 2).re) * x))
      =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 3

/-- Theorem 11: `μ⋆(n) ≠ 0` if and only if every prime exponent of `n` is at
most `3`; the set `S = {n : μ⋆(n) ≠ 0}` has natural density
`∏_p (1 - p^{-4}) = 1/ζ(4)`, equivalently `∑_{n ≤ x} μ⋆(n)² ∼ x/ζ(4)`.
`μ⋆` enters as any `m` with `1 ⋆ m = ε`.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 11
(`integers-2026-A56-thm-11`). -/
public theorem_wanted squareSplitMoebius_support_density (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) :
    (∀ n ≠ 0, m n ≠ 0 ↔ ∀ p, n.factorization p ≤ 3) ∧
    Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun n => m n ≠ 0).card : ℝ) / N) atTop
      (𝓝 (∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4))) ∧
    ((∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 4) : ℝ) : ℂ) = 1 / riemannZeta 4 ∧
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖m n‖ ^ 2) ~[atTop]
      fun x => x / (riemannZeta 4).re

/-- Theorem 6, the parts about the explicit function: for `α ∈ ℂ` let
`f(n) = σ_α(u(n)) σ_{2α}(v(n))` with `n = u(n) v(n)²` and the classical divisor sum
`σ_β(m) = ∑_{d ∣ m} d^β` (complex powers). Then `f` is multiplicative, for every prime `p`
`f(p^{2b}) = 1 + p^{2α} + ⋯ + p^{2bα}` and `f(p^{2b+1}) = (1 + p^α)(1 + p^{2α} + ⋯ + p^{2bα})`,
and for `Re s > max(1, 1 + Re α)` the local factors are
`∑_k f(p^k)/p^{ks} = (1 + p^{-s} + p^{-(s-α)}) / ((1 - p^{-2s})(1 - p^{-(2s-2α)}))` and
`∑ f(n)/n^s = ζ(2s) ζ(2s - 2α) ∏_p (1 + p^{-s} + p^{-(s-α)})`, absolutely convergent. The
paper's identification of `f` with its `σ⋆,α` (defined only in the paper body) is not stated.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 6
(`integers-2026-A56-thm-6`). -/
public theorem_wanted squareSplitSigma_multiplicative_eulerProduct (α : ℂ) :
    let σ : ℂ → ℕ → ℂ := fun β m => ∑ d ∈ m.divisors, (d : ℂ) ^ β
    let f : ℕ → ℂ := fun n => σ α (squareSplitU n) * σ (2 * α) (squareSplitV n)
    f 1 = 1 ∧ (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) ∧
    (∀ p : ℕ, p.Prime → ∀ b : ℕ,
      f (p ^ (2 * b)) = ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α) ∧
      f (p ^ (2 * b + 1)) =
        (1 + (p : ℂ) ^ α) * ∑ j ∈ Finset.range (b + 1), (p : ℂ) ^ (2 * j * α)) ∧
    ∀ s : ℂ, max 1 (1 + α.re) < s.re →
      (∀ p : ℕ, p.Prime →
        HasSum (fun k : ℕ => f (p ^ k) * (p : ℂ) ^ (-(k * s)))
          ((1 + (p : ℂ) ^ (-s) + (p : ℂ) ^ (-(s - α))) /
            ((1 - (p : ℂ) ^ (-(2 * s))) * (1 - (p : ℂ) ^ (-(2 * s - 2 * α)))))) ∧
      LSeriesSummable f s ∧
      LSeries f s = riemannZeta (2 * s) * riemannZeta (2 * s - 2 * α) *
        ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (-(s - α)))

end

end MetaMathlibExt
