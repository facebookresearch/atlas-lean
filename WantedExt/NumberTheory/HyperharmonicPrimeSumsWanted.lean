/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WantedExt.NumberTheory.GeneralizedHarmonicGammaWanted

/-!
# Sums over primes II (statements)

Statement-only targets from Rusen Li, *Sums over Primes II*: the asymptotic of hyperharmonic
numbers, Jakimczuk's summation lemma, the asymptotics of the `n`-th (squarefree) number with
exactly `k` prime factors, two power-log summation asymptotics, the explicit formulas and
asymptotics of the generalized (alternating) hyperharmonic numbers `H_n^{(p,r)}` and
`H_n^{(p,r,i)}` (`i = 1, 2, 3`), and the asymptotics of sums over primes and over squarefree
numbers with `k` prime factors weighted by powers of these numbers.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset

@[expose] public section

/-- Hyperharmonic numbers (Conway–Guy): `h_n^{(0)} = 1/n` and
`h_n^{(r+1)} = ∑_{k=1}^{n} h_k^{(r)}`, so `h_n^{(1)} = H_n`. The value at `n = 0` is `0` for
every order.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public def hyperharmonic : ℕ → ℕ → ℚ
  | 0, n => 1 / n
  | r + 1, n => ∑ k ∈ Icc 1 n, hyperharmonic r k

/-- The defining recursion `h_n^{(r+1)} = ∑_{k=1}^{n} h_k^{(r)}`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_succ (r n : ℕ) :
    hyperharmonic (r + 1) n = ∑ k ∈ Icc 1 n, hyperharmonic r k := rfl

/-- First-order hyperharmonic numbers are the harmonic numbers: `h_n^{(1)} = H_n`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_one (n : ℕ) : hyperharmonic 1 n = harmonic n := by
  induction n with
  | zero => simp [hyperharmonic]
  | succ n ih =>
    rw [harmonic_succ, ← ih, hyperharmonic, hyperharmonic, Finset.sum_Icc_succ_top (by omega)]
    simp [hyperharmonic]

/-- Small value `h_2^{(2)} = H_1 + H_2 = 5/2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (hyperharmonic numbers `h_n^{(r)}`, after Mező). -/
public theorem hyperharmonic_two_two : hyperharmonic 2 2 = 5 / 2 := by
  simp [hyperharmonic, Finset.sum_Icc_succ_top]
  norm_num

/-- Lemma 1 (Mező): for a fixed order `r ≥ 1`, `h_n^{(r)} ∼ n^{r-1} log n / (r-1)!` as
`n → ∞`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 1 (`jis-2024-24.4.1-lem-1`). -/
public theorem_wanted hyperharmonic_isEquivalent (r : ℕ) (hr : 1 ≤ r) :
    (fun n : ℕ => (hyperharmonic r n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * Real.log n / (r - 1).factorial

/-- Lemma 7 (Jakimczuk): if `∑ a_i` and `∑ b_i` are series of positive terms with
`a_i ∼ b_i` and `∑ b_i` diverges, then `∑_{i=1}^{n} a_i ∼ ∑_{i=1}^{n} b_i`. Divergence of a
series of positive terms is stated as the partial sums tending to `+∞`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 7 (`jis-2024-24.4.1-lem-7`). -/
public theorem_wanted sum_isEquivalent_of_isEquivalent (a b : ℕ → ℝ)
    (ha : ∀ i, 1 ≤ i → 0 < a i) (hb : ∀ i, 1 ≤ i → 0 < b i) (hab : a ~[atTop] b)
    (hdiv : Tendsto (fun n => ∑ i ∈ Icc 1 n, b i) atTop atTop) :
    (fun n => ∑ i ∈ Icc 1 n, a i) ~[atTop] fun n => ∑ i ∈ Icc 1 n, b i

/-- Lemma 8 (Hardy–Wright, Li): let `p_{n,k}` be the `n`-th squarefree number with exactly `k`
prime factors and `q_{n,k}` the `n`-th number with exactly `k` prime factors counted with
multiplicity (`Ω = k`, Hardy–Wright's `τ_k`). For `k ≥ 1`,
`p_{n,k} ∼ q_{n,k} ∼ (k-1)! n log n / (log log n)^{k-1}`,
`p_{n,k} (log log p_{n,k})^{k-1} ∼ q_{n,k} (log log q_{n,k})^{k-1} ∼ (k-1)! n log n`,
and for `k = 1`, `p_n ∼ n log n` for the `n`-th prime. The `n`-th element (from `n = 1`) is
`Nat.nth _ (n - 1)`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 8 (`jis-2024-24.4.1-lem-8`). -/
public theorem_wanted nth_kPrimeFactors_isEquivalent (k : ℕ) (hk : 1 ≤ k) :
    let p : ℕ → ℝ := fun n =>
      (Nat.nth (fun m => Squarefree m ∧ m.primeFactors.card = k) (n - 1) : ℝ)
    let q : ℕ → ℝ := fun n =>
      (Nat.nth (fun m => ArithmeticFunction.cardFactors m = k) (n - 1) : ℝ)
    (p ~[atTop] q) ∧
      (q ~[atTop] fun n : ℕ =>
        (k - 1).factorial * n * Real.log n / Real.log (Real.log n) ^ (k - 1)) ∧
      ((fun n => p n * Real.log (Real.log (p n)) ^ (k - 1)) ~[atTop]
        fun n => q n * Real.log (Real.log (q n)) ^ (k - 1)) ∧
      ((fun n => q n * Real.log (Real.log (q n)) ^ (k - 1)) ~[atTop]
        fun n : ℕ => (k - 1).factorial * n * Real.log n) ∧
      ((fun n : ℕ => (Nat.nth Nat.Prime (n - 1) : ℝ)) ~[atTop]
        fun n : ℕ => n * Real.log n)

/-- Lemma 9: for `m, n, k ∈ ℕ`, as `x → ∞`,
`∑_{ℓ=1}^{x} ℓ^m (log ℓ)^n ∼ x^{m+1} (log x)^n / (m+1)` and
`∑_{ℓ=1}^{x} ℓ^m (log ℓ)^n / (log log ℓ)^k ∼ x^{m+1} (log x)^n / ((m+1)(log log x)^k)`.
The terms `ℓ = 1, 2` of the second sum use Lean's conventions for `log 0` and division by `0`;
finitely many terms do not affect the asymptotic.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 9 (`jis-2024-24.4.1-lem-9`). -/
public theorem_wanted sum_pow_mul_log_pow_isEquivalent (m n k : ℕ) :
    ((fun x : ℕ => ∑ l ∈ Icc 1 x, (l : ℝ) ^ m * Real.log l ^ n) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (m + 1) * Real.log x ^ n / (m + 1)) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (l : ℝ) ^ m * Real.log l ^ n / Real.log (Real.log l) ^ k) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (m + 1) * Real.log x ^ n /
        ((m + 1) * Real.log (Real.log x) ^ k))


/-- Alternating generalized harmonic numbers `H̄_n^{(s)} = ∑_{j=1}^n (-1)^{j-1} / j^s` for real `s`;
for `s = -p` with `p ∈ ℕ` this is `∑_{j=1}^n (-1)^{j-1} j^p`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}` and `H̄_n^{(-p)}`). -/
public noncomputable def alternatingGeneralizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (-1 : ℝ) ^ (j - 1) * ((j : ℝ) ^ s)⁻¹

/-- `H̄_0^{(s)} = 0`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definition of `H̄_n^{(p)}`). -/
@[simp]
public theorem alternatingGeneralizedHarmonic_zero (s : ℝ) :
    alternatingGeneralizedHarmonic s 0 = 0 := by
  simp [alternatingGeneralizedHarmonic]

/-- Iterated partial sums of order `r ≥ 1` of a base sequence `b`: order `1` is `b` itself and
order `r + 1` at `n` is `∑_{k=1}^n ε_k · (order r at k)` with `ε_k = (-1)^{k-1}` when `alt` and
`ε_k = 1` otherwise; the value at order `0` is `0` and is not used. With `b = H^{(p)}` this gives
the generalized hyperharmonic numbers `H_n^{(p,r)}` (`alt = false`) and the type I alternating
ones `H_n^{(p,r,1)}` (`alt = true`); with `b = H̄^{(p)}` it gives types II (`alt = false`) and
III (`alt = true`).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`, `i = 1, 2, 3`). -/
public noncomputable def signedIteratedPartialSum (alt : Bool) (b : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, n => b n
  | r + 2, n => ∑ k ∈ Icc 1 n, (if alt then (-1 : ℝ) ^ (k - 1) else 1) *
      signedIteratedPartialSum alt b (r + 1) k

/-- Order `1` of the iterated partial sums is the base sequence.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (`H_n^{(p,1)} = H_n^{(p)}`, `H_n^{(p,1,1)} = H_n^{(p)}`,
`H_n^{(p,1,2)} = H_n^{(p,1,3)} = H̄_n^{(p)}`). -/
public theorem signedIteratedPartialSum_one (alt : Bool) (b : ℕ → ℝ) (n : ℕ) :
    signedIteratedPartialSum alt b 1 n = b n := rfl

/-- The defining recursion of the iterated partial sums.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`). -/
public theorem signedIteratedPartialSum_succ (alt : Bool) (b : ℕ → ℝ) (r n : ℕ) :
    signedIteratedPartialSum alt b (r + 2) n = ∑ k ∈ Icc 1 n,
      (if alt then (-1 : ℝ) ^ (k - 1) else 1) * signedIteratedPartialSum alt b (r + 1) k := rfl

/-- The alternating zeta function at a positive integer:
`ζ̄(p) = ∑_{n ≥ 1} (-1)^{n-1} / n^p = (1 - 2^{1-p}) ζ(p)` for `p ≥ 2`, and `ζ̄(1) = log 2`.
The case `p = 0` is not used.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
public noncomputable def alternatingZeta (p : ℕ) : ℝ :=
  if p = 1 then Real.log 2 else (1 - 2 ^ (1 - (p : ℝ))) * ∑' n : ℕ, 1 / (n : ℝ) ^ p

/-- `ζ̄(1) = log 2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (definition of `ζ̄(s)`). -/
@[simp]
public theorem alternatingZeta_one : alternatingZeta 1 = Real.log 2 := by
  simp [alternatingZeta]

/-- The coefficients `a(r, m, j)` of Lemma 3, defined by `a(1, 0, 0) = 1` and, for `r ≥ 1`,
`a(r+1, r, 0) = -∑_{m=0}^{r-1} a(r, m, r-m-1) / (r - m)`,
`a(r+1, m, ℓ) = ∑_{j=ℓ-1}^{r-1-m} a(r, m, j) / (j+1) · C(j+1, j-ℓ+1) B_{j-ℓ+1}`
(`0 ≤ m ≤ r-1`, `1 ≤ ℓ ≤ r-m`), and
`a(r+1, m, 0) = -∑_{y=0}^{m} ∑_{j=max(0, m-y-1)}^{r-1-y} a(r, y, j) D(m, j, y)` (`0 ≤ m ≤ r-1`) with
`D(m, j, y) = ∑_{ℓ=max(0, m-y-1)}^{j} 1/(j+1) · C(j+1, j-ℓ) B_{j-ℓ} C(ℓ+1, m-y) (-1)^{1+ℓ-m+y}`
(the paper writes `D(r, m, j, y)`; it does not depend on `r`). All other entries are `0`.
`B_n = bernoulli' n` (`B_1 = 1/2`), the numbers fixed by the paper's recurrence
`∑_{j=0}^k C(k+1, j) B_j = k + 1`. Here `r + 2` is the paper's `r + 1` with the paper's `r` equal
to `r + 1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (quoting Li, *Euler sums of generalized hyperharmonic numbers*). -/
public def liCoeffA : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 0
  | 1, m, j => if m = 0 ∧ j = 0 then 1 else 0
  | r + 2, m, l =>
    if m = r + 1 ∧ l = 0 then
      -∑ m' ∈ range (r + 1), liCoeffA (r + 1) m' (r - m') / ((r + 1 - m' : ℕ) : ℚ)
    else if m ≤ r ∧ 1 ≤ l ∧ l ≤ r + 1 - m then
      ∑ j ∈ Icc (l - 1) (r - m), liCoeffA (r + 1) m j / ((j + 1 : ℕ) : ℚ) *
        ((j + 1).choose (j + 1 - l) : ℚ) * bernoulli' (j + 1 - l)
    else if m ≤ r ∧ l = 0 then
      -∑ y ∈ range (m + 1), ∑ j ∈ Icc (m - y - 1) (r - y), liCoeffA (r + 1) y j *
        ∑ i ∈ Icc (m - y - 1) j, 1 / ((j + 1 : ℕ) : ℚ) * ((j + 1).choose (j - i) : ℚ) *
          bernoulli' (j - i) * ((i + 1).choose (m - y) : ℚ) * (-1) ^ (1 + i + y - m)
    else 0

/-- Initial value `a(1, 0, 0) = 1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_one_zero_zero : liCoeffA 1 0 0 = 1 := by
  simp [liCoeffA]

/-- Small value `a(2, 1, 0) = -a(1, 0, 0) = -1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3. -/
public theorem liCoeffA_two_one_zero : liCoeffA 2 1 0 = -1 := by
  simp [liCoeffA]

/-- `c(m, j) = 1/(m+1) · C(m+1, m+1-j) B_{m+1-j}` (`0` for `j > m + 1`), with `B = bernoulli'`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffC (m j : ℕ) : ℚ :=
  if j ≤ m + 1 then
    1 / ((m + 1 : ℕ) : ℚ) * ((m + 1).choose (m + 1 - j) : ℚ) * bernoulli' (m + 1 - j)
  else 0

/-- `c(0, 0) = B_1 = 1/2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffC_zero_zero : liCoeffC 0 0 = 1 / 2 := by
  simp [liCoeffC]

/-- `d(m, j) = 1/(m+1) ∑_{k=j-1}^{m} C(m+1, m-k) B_{m-k} C(1+k, j) (-1)^{1+k-j}`, with
`B = bernoulli'` (for `j = 0` the sum starts at `k = 0`).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffD (m j : ℕ) : ℚ :=
  1 / ((m + 1 : ℕ) : ℚ) * ∑ k ∈ Icc (j - 1) m,
    ((m + 1).choose (m - k) : ℚ) * bernoulli' (m - k) * ((1 + k).choose j : ℚ) * (-1) ^ (1 + k - j)

/-- `d(0, 1) = 1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffD_zero_one : liCoeffD 0 1 = 1 := by
  simp [liCoeffD]

/-- `c₁(m, j) = 1/(2(m+1)) ∑_{k=0}^{m-j} C(m+1, k) B_k 2^k C(m+1-k, j) (-1)^{m-k-j}` for `j ≤ m`
(`0` otherwise), with `B = bernoulli'`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffC1 (m j : ℕ) : ℚ :=
  if j ≤ m then 1 / (2 * ((m + 1 : ℕ) : ℚ)) * ∑ k ∈ range (m - j + 1),
    ((m + 1).choose k : ℚ) * bernoulli' k * 2 ^ k * ((m + 1 - k).choose j : ℚ) * (-1) ^ (m - k - j)
  else 0

/-- `c₁(0, 0) = 1/2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffC1_zero_zero : liCoeffC1 0 0 = 1 / 2 := by
  simp [liCoeffC1]

/-- `d₁(m, j) = ∑_{k=j}^{m} C(k, j) (-1)^{k-j} c₁(m, k)`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public def liCoeffD1 (m j : ℕ) : ℚ :=
  ∑ k ∈ Icc j m, (k.choose j : ℚ) * (-1) ^ (k - j) * liCoeffC1 m k

/-- `d₁(0, 0) = c₁(0, 0) = 1/2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 4. -/
public theorem liCoeffD1_zero_zero : liCoeffD1 0 0 = 1 / 2 := by
  simp [liCoeffD1, liCoeffC1]

/-- The coefficients `b₁(r, m, j, k)` (`k = 0, 1, 2, 3`) of Definition 5, with
`g(r) = (2r - (-1)^r - 3)/4 = ⌊(r-1)/2⌋`: `b₁(1, 0, 0, 2) = 1`, all other order-`1` values `0`,
and for `r ≥ 1` the order-`(r+1)` values are given by the paper's recurrences (from `k = 2, 3` to
`k = 0, 1` when `r` is odd, from `k = 0, 1` to `k = 2, 3` when `r` is even), every entry outside
the ranges the recurrences cover being `0`. The paper's boundary values (`b₁(r, ·, ·, 0) =
b₁(r, ·, ·, 1) = 0` for odd `r`, `b₁(r, ·, ·, 2) = b₁(r, ·, ·, 3) = 0` for even `r`, and
`b₁(r, m, j, 3) = 0` for odd `r` and `m + j = g(r)`) are consequences. In the recurrences the
first index is the power of `n` and the second the shift of `p`, as in Lemma 6. Here `r + 2` is
the paper's `r + 1` with the paper's `r` equal to `r + 1`, and `G = g(r + 1) = r / 2`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5 (with `c, d, c₁, d₁` from Definition 4). -/
public def liCoeffB1 : ℕ → ℕ → ℕ → ℕ → ℚ
  | 0, _, _, _ => 0
  | 1, m, j, k => if m = 0 ∧ j = 0 ∧ k = 2 then 1 else 0
  | r + 2, m, j, k =>
    let G := r / 2
    let P := liCoeffB1 (r + 1)
    if r % 2 = 0 then
      -- the paper's `r = r + 1` is odd: new values of types 0 and 1
      if k = 0 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc m G, P l j 2 * liCoeffC1 l m
        else if m = 0 ∧ j ≤ G then ∑ l ∈ range (G - j + 1), P l j 2 * liCoeffC1 l 0
        else 0
      else if k = 1 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc (m - 1) (G - 1), P l j 3 * liCoeffC l m
        else if m = 0 ∧ j ≤ G then
          (∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' then P m' j₁ 2 * liCoeffD1 m' (j - j₁) else 0) +
            (∑ m' ∈ range (G - j + 1), P m' j 2 * liCoeffD1 m' 0) + P 0 j 3 -
            ∑ m' ∈ range G, ∑ j₁ ∈ range (G - m'),
              if j₁ < j ∧ j - j₁ ≤ m' + 1 then P m' j₁ 3 * liCoeffD m' (j - j₁) else 0
        else 0
      else 0
    else
      -- the paper's `r = r + 1` is even: new values of types 2 and 3
      if k = 2 then
        if 1 ≤ m ∧ m ≤ G + 1 ∧ j ≤ G + 1 - m then ∑ l ∈ Icc (m - 1) G, P l j 0 * liCoeffC l m
        else if m = 0 ∧ j ≤ G + 1 then
          -(∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' + 1 then P m' j₁ 0 * liCoeffD m' (j - j₁) else 0) +
            (∑ m' ∈ range (G - j + 1), P m' j 1 * liCoeffD1 m' 0) + P 0 j 0 +
            ∑ m' ∈ range (G + 1), ∑ j₁ ∈ range (G - m' + 1),
              if j₁ < j ∧ j - j₁ ≤ m' then P m' j₁ 1 * liCoeffD1 m' (j - j₁) else 0
        else 0
      else if k = 3 then
        if 1 ≤ m ∧ m ≤ G ∧ j ≤ G - m then ∑ l ∈ Icc m G, P l j 1 * liCoeffC1 l m
        else if m = 0 ∧ j ≤ G then ∑ l ∈ range (G - j + 1), P l j 1 * liCoeffC1 l 0
        else 0
      else 0

/-- Initial value `b₁(1, 0, 0, 2) = 1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5. -/
public theorem liCoeffB1_one_zero_zero_two : liCoeffB1 1 0 0 2 = 1 := by
  simp [liCoeffB1]

/-- Initial value `b₁(1, 0, 0, 3) = 0`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Definition 5. -/
public theorem liCoeffB1_one_zero_zero_three : liCoeffB1 1 0 0 3 = 0 := by
  simp [liCoeffB1]


/-- Lemma 2: for `p ≥ 2` and order `r ≥ 1`, the generalized hyperharmonic numbers satisfy
`H_n^{(p,r)} ∼ n^{r-1} ζ(p) / (r-1)!` as `n → ∞`, where
`H_n^{(p,r)} = signedIteratedPartialSum false (generalizedHarmonic p) r n` and `ζ(p) = ∑ 1/n^p`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 2 (`jis-2024-24.4.1-lem-2`). -/
public theorem_wanted generalizedHyperharmonic_isEquivalent {p r : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ r) :
    (fun n : ℕ => signedIteratedPartialSum false (generalizedHarmonic p) r n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * (∑' i : ℕ, 1 / (i : ℝ) ^ p) / (r - 1).factorial

/-- Lemma 3: for `r, n, p ≥ 1`, the type II generalized alternating hyperharmonic numbers satisfy
`H_n^{(p,r,2)} = ∑_{m=0}^{r-1} ∑_{j=0}^{r-1-m} a(r, m, j) n^j H̄_n^{(p-m)}`, with `a = liCoeffA`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 3 (`jis-2024-24.4.1-lem-3`). -/
public theorem_wanted alternatingHyperharmonic_typeII_eq_sum {r n p : ℕ} (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n =
      ∑ m ∈ range r, ∑ j ∈ range (r - m),
        (liCoeffA r m j : ℝ) * (n : ℝ) ^ j * alternatingGeneralizedHarmonic ((p : ℝ) - m) n

/-- Lemma 6: for `r, n, p ≥ 1` and `g(r) = (2r - (-1)^r - 3)/4 = ⌊(r-1)/2⌋`, the type I and type
III generalized alternating hyperharmonic numbers are
`H_n^{(p,r,1)} = ∑_{m=0}^{g(r)} ∑_{j=0}^{g(r)-m} (b₁(r,j,m,0)(-1)^{n-1} H_n^{(p-m)}
+ b₁(r,j,m,1) H̄_n^{(p-m)} + b₁(r,j,m,2) H_n^{(p-m)} + b₁(r,j,m,3)(-1)^{n-1} H̄_n^{(p-m)}) n^j`
and the same with `H` and `H̄` exchanged for `H_n^{(p,r,3)}`, with `b₁ = liCoeffB1`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 6 (`jis-2024-24.4.1-lem-6`). -/
public theorem_wanted alternatingHyperharmonic_typeI_typeIII_eq_sum {r n p : ℕ} (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    let H := fun m : ℕ => generalizedHarmonic ((p : ℝ) - m) n
    let Hb := fun m : ℕ => alternatingGeneralizedHarmonic ((p : ℝ) - m) n
    let s : ℝ := (-1) ^ (n - 1)
    signedIteratedPartialSum true (generalizedHarmonic p) r n =
        ∑ m ∈ range ((r - 1) / 2 + 1), ∑ j ∈ range ((r - 1) / 2 - m + 1),
          ((liCoeffB1 r j m 0 : ℝ) * s * H m + (liCoeffB1 r j m 1 : ℝ) * Hb m +
            (liCoeffB1 r j m 2 : ℝ) * H m + (liCoeffB1 r j m 3 : ℝ) * s * Hb m) * (n : ℝ) ^ j ∧
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic p) r n =
        ∑ m ∈ range ((r - 1) / 2 + 1), ∑ j ∈ range ((r - 1) / 2 - m + 1),
          ((liCoeffB1 r j m 0 : ℝ) * s * Hb m + (liCoeffB1 r j m 1 : ℝ) * H m +
            (liCoeffB1 r j m 2 : ℝ) * Hb m + (liCoeffB1 r j m 3 : ℝ) * s * H m) * (n : ℝ) ^ j

/-- Lemma 10: for `y ≥ 1` and `p ≥ 2`, the type I numbers `H_n^{(p,r,1)}` satisfy
`H_n^{(1,2y+1,1)} ∼ n^y log n / (2^y y!)`, `H_n^{(p,2y+1,1)} ∼ n^y ζ(p) / (2^y y!)`,
`H_n^{(1,2y,1)} ∼ (-1)^{n-1} n^{y-1} log n / (2^y (y-1)!)`,
`H_{2n}^{(p,2y,1)} ∼ -n^{y-1} (ζ(p) - ζ̄(p)) / (2 (y-1)!)` and
`H_{2n-1}^{(p,2y,1)} ∼ n^{y-1} (ζ(p) + ζ̄(p)) / (2 (y-1)!)`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 10 (`jis-2024-24.4.1-lem-10`). -/
public theorem_wanted alternatingHyperharmonic_typeI_isEquivalent {y p : ℕ} (hy : 1 ≤ y)
    (hp : 2 ≤ p) :
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    let ζp : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ p
    ((fun n : ℕ => HI 1 (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * Real.log n / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI p (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * ζp / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI 1 (2 * y) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (-1) ^ (n - 1) * Real.log n /
        ((2 ^ y * (y - 1).factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HI p (2 * y) (2 * n)) ~[atTop]
      fun n : ℕ => -((n : ℝ) ^ (y - 1) * (ζp - alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))) ∧
    ((fun n : ℕ => HI p (2 * y) (2 * n - 1)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp + alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))

/-- Lemma 13: for `r, p ≥ 1`, the type II numbers satisfy
`H_n^{(p,r,2)} ∼ n^{r-1} ζ̄(p) / (r-1)!` (with `ζ̄(1) = log 2`).

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 13 (`jis-2024-24.4.1-lem-13`). -/
public theorem_wanted alternatingHyperharmonic_typeII_isEquivalent {r p : ℕ} (hr : 1 ≤ r)
    (hp : 1 ≤ p) :
    (fun n : ℕ => signedIteratedPartialSum false (alternatingGeneralizedHarmonic p) r n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (r - 1) * alternatingZeta p / (r - 1).factorial

/-- Lemma 16: for `y, p ≥ 1`, the type III numbers satisfy
`H_n^{(p,2y+1,3)} ∼ n^y ζ̄(p) / (2^y y!)`, `H_n^{(1,2y,3)} ∼ n^{y-1} log n / (2^y (y-1)!)`, and for
`p ≥ 2`, `H_{2n}^{(p,2y,3)} ∼ n^{y-1} (ζ(p) - ζ̄(p)) / (2 (y-1)!)` and
`H_{2n-1}^{(p,2y,3)} ∼ n^{y-1} (ζ(p) + ζ̄(p)) / (2 (y-1)!)`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Lemma 16 (`jis-2024-24.4.1-lem-16`). -/
public theorem_wanted alternatingHyperharmonic_typeIII_isEquivalent {y p : ℕ} (hy : 1 ≤ y)
    (hp : 1 ≤ p) :
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    let ζp : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ p
    ((fun n : ℕ => HIII p (2 * y + 1) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ y * alternatingZeta p / ((2 ^ y * y.factorial : ℕ) : ℝ)) ∧
    ((fun n : ℕ => HIII 1 (2 * y) n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * Real.log n / ((2 ^ y * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp - alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ)) ∧
    (2 ≤ p → (fun n : ℕ => HIII p (2 * y) (2 * n - 1)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (y - 1) * (ζp + alternatingZeta p) /
        ((2 * (y - 1).factorial : ℕ) : ℝ))

/-- Theorem 15: for `q₁, q₂, α, β, m, k, s, n, r₁, r₂ ≥ 1` with `q₁ ≥ 2` and
`E = m(r₁-1) + n(s-1) + β(r₂-1)`, `A = α + E + 1`,
`∑_{ℓ ≤ x} p_{ℓ,k}^α (H_ℓ^{(q₁,r₁)})^m (h_ℓ^{(s)})^n (H_ℓ^{(q₂,r₂,2)})^β ∼ ((k-1)!)^α ζ(q₁)^m
ζ̄(q₂)^β (log x)^{α+n} x^A / (((r₁-1)!)^m ((s-1)!)^n ((r₂-1)!)^β A (log log x)^{α(k-1)})`, and
the same sum over `p_{ℓ,k} ≤ x` is `∼ ζ(q₁)^m ζ̄(q₂)^β x^A (log log x)^{(E+1)(k-1)} /
(A ((r₁-1)!)^m ((s-1)!)^n ((r₂-1)!)^β ((k-1)!)^{E+1} (log x)^{m(r₁-1)+n(s-2)+β(r₂-1)+1})`; the last
exponent may be negative (`s = 1`), so it is an integer power. Here `h^{(s)} = hyperharmonic s`,
`p_{ℓ,k}` is the `ℓ`th squarefree number with exactly `k` prime factors, and `x` is natural.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 15 (`jis-2024-24.4.1-thm-15`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_hyperharmonic_products_isEquivalent
    {q₁ q₂ α β m k s n r₁ r₂ : ℕ} (hq₁ : 2 ≤ q₁) (hq₂ : 1 ≤ q₂) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : 1 ≤ n) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let f : ℕ → ℝ := fun l =>
      (pk l : ℝ) ^ α * (signedIteratedPartialSum false (generalizedHarmonic q₁) r₁ l) ^ m *
        (hyperharmonic s l : ℝ) ^ n *
        (signedIteratedPartialSum false (alternatingGeneralizedHarmonic q₂) r₂ l) ^ β
    let E : ℕ := m * (r₁ - 1) + n * (s - 1) + β * (r₂ - 1)
    let Z : ℝ := (∑' i : ℕ, 1 / (i : ℝ) ^ q₁) ^ m * alternatingZeta q₂ ^ β
    let D : ℝ := ((r₁ - 1).factorial : ℝ) ^ m * ((s - 1).factorial : ℝ) ^ n *
      ((r₂ - 1).factorial : ℝ) ^ β
    ((fun x : ℕ => ∑ l ∈ Icc 1 x, f l) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * Z * Real.log x ^ (α + n) *
        (x : ℝ) ^ (α + E + 1) /
          (D * ((α + E + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x), f l) ~[atTop]
      fun x : ℕ => Z * (x : ℝ) ^ (α + E + 1) * Real.log (Real.log x) ^ ((E + 1) * (k - 1)) /
        (((α + E + 1 : ℕ) : ℝ) * D * ((k - 1).factorial : ℝ) ^ (E + 1) *
          Real.log x ^ ((m : ℤ) * ((r₁ : ℤ) - 1) + (n : ℤ) * ((s : ℤ) - 2) +
            (β : ℤ) * ((r₂ : ℤ) - 1) + 1)))

/-- Theorem 11: for `α, m, q, y ≥ 1` with `q ≥ 2`, the fourteen asymptotics of `∑ p_ℓ^α
(H_ℓ^{(1,2y+1,1)})^m`, `∑ p_ℓ^α (H_ℓ^{(q,2y+1,1)})^m`, `∑ p_ℓ^α ((-1)^{ℓ-1}
H_ℓ^{(1,2y,1)})^m`, `∑ p_ℓ^α (H_{2ℓ-1}^{(1,2y,1)})^m`, `∑ p_ℓ^α (-H_{2ℓ}^{(1,2y,1)})^m`, `∑
p_ℓ^α (H_{2ℓ-1}^{(q,2y,1)})^m` and `∑ p_ℓ^α (-H_{2ℓ}^{(q,2y,1)})^m`, each over `ℓ ≤ x` and
over `p_ℓ ≤ x`, in the paper's order. The exponent `m(y-2)+1` of `log x` may be negative, so
those powers are integer powers. Sums run over `ℓ ≤ x` (`ℓ ∈ [1, x]`) or over `p_ℓ ≤ x` for
natural `x → ∞` (the sums depend on `⌊x⌋` only); `p_ℓ = Nat.nth Nat.Prime (ℓ - 1)`, `p_{ℓ,k}`
is the `ℓ`th squarefree number with exactly `k` prime factors, `H_n^{(p,r,i)}` is
`signedIteratedPartialSum` over `generalizedHarmonic p` (type I) or `alternatingGeneralizedHarmonic
p` (types II, III), `ζ(q) = ∑ 1/n^q`, and `ζ̄ = alternatingZeta`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 11 (`jis-2024-24.4.1-thm-11`). -/
public theorem_wanted sum_primes_pow_mul_alternatingHyperharmonic_typeI_isEquivalent
    {α m q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1)))

/-- Theorem 12: the analogues of Theorem 11 with `p_ℓ` replaced by `p_{ℓ,k}` (`k ≥ 1`), sums over
`ℓ ≤ x` and over `p_{ℓ,k} ≤ x`. Corrected reading: in the seventh item the paper prints the
second sum `∑ p_{ℓ,k}^α (-H_{2ℓ}^{(1,2y,1)})^m` over `p_{ℓ,k} ≤ x` but gives it the `ℓ ≤ x`
asymptotic of the first sum (and the `p_{ℓ,k} ≤ x` version is the eighth item), so it is read
as a sum over `ℓ ≤ x`, as in Theorem 11. Sums run over `ℓ ≤ x` (`ℓ ∈ [1, x]`) or over `p_ℓ ≤
x` for natural `x → ∞` (the sums depend on `⌊x⌋` only); `p_ℓ = Nat.nth Nat.Prime (ℓ - 1)`,
`p_{ℓ,k}` is the `ℓ`th squarefree number with exactly `k` prime factors, `H_n^{(p,r,i)}` is
`signedIteratedPartialSum` over `generalizedHarmonic p` (type I) or `alternatingGeneralizedHarmonic
p` (types II, III), `ζ(q) = ∑ 1/n^q`, and `ζ̄ = alternatingZeta`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 12 (`jis-2024-24.4.1-thm-12`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeI_isEquivalent
    {α m k q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : 1 ≤ k) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HI := fun (s : ℝ) (r n : ℕ) => signedIteratedPartialSum true (generalizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI 1 (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * y + 1) * Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * ζq ^ m *
        (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI q (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ζq ^ m * (x : ℝ) ^ (α + m * y + 1) *
        Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * ((-1 : ℝ) ^ (l - 1) * HI 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
            ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI 1 (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (-HI 1 (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HI q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (-HI q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1)))

/-- Theorem 14: for `α, m, q, k, r ≥ 1`, the asymptotics of `∑ p_ℓ^α (H_ℓ^{(q,r,2)})^m` over `ℓ ≤
x` and over `p_ℓ ≤ x`, and of `∑ p_{ℓ,k}^α (H_ℓ^{(q,r,2)})^m` over `ℓ ≤ x` and over `p_{ℓ,k} ≤
x`. Sums run over `ℓ ≤ x` (`ℓ ∈ [1, x]`) or over `p_ℓ ≤ x` for natural `x → ∞` (the sums
depend on `⌊x⌋` only); `p_ℓ = Nat.nth Nat.Prime (ℓ - 1)`, `p_{ℓ,k}` is the `ℓ`th squarefree
number with exactly `k` prime factors, `H_n^{(p,r,i)}` is `signedIteratedPartialSum` over
`generalizedHarmonic p` (type I) or `alternatingGeneralizedHarmonic p` (types II, III), `ζ(q)
= ∑ 1/n^q`, and `ζ̄ = alternatingZeta`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 14 (`jis-2024-24.4.1-thm-14`). -/
public theorem_wanted sum_pow_mul_alternatingHyperharmonic_typeII_isEquivalent
    {α m q k r : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hq : 1 ≤ q) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let HII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum false (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m * (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log x ^ (α) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m * (x : ℝ) ^ (α + m * (r - 1) + 1) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (r - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * alternatingZeta q ^ m *
        (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log x ^ (α) /
        (((r - 1).factorial : ℝ) ^ m * ((α + m * (r - 1) + 1 : ℕ) : ℝ) *
          Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HII q (r) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta q ^ m *
        (x : ℝ) ^ (α + m * (r - 1) + 1) * Real.log (Real.log x) ^ ((m * (r - 1) + 1) * (k - 1)) /
        (((r - 1).factorial : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (r - 1) + 1) *
          ((α + m * (r - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (r - 1) + 1)))

/-- Theorem 17: for `α, m, p, q, y ≥ 1` with `q ≥ 2`, the eight asymptotics of `∑ p_ℓ^α
(H_ℓ^{(p,2y+1,3)})^m`, `∑ p_ℓ^α (H_ℓ^{(1,2y,3)})^m`, `∑ p_ℓ^α (H_{2ℓ-1}^{(q,2y,3)})^m` and `∑
p_ℓ^α (H_{2ℓ}^{(q,2y,3)})^m`, each over `ℓ ≤ x` and over `p_ℓ ≤ x`. Sums run over `ℓ ≤ x` (`ℓ
∈ [1, x]`) or over `p_ℓ ≤ x` for natural `x → ∞` (the sums depend on `⌊x⌋` only); `p_ℓ =
Nat.nth Nat.Prime (ℓ - 1)`, `p_{ℓ,k}` is the `ℓ`th squarefree number with exactly `k` prime
factors, `H_n^{(p,r,i)}` is `signedIteratedPartialSum` over `generalizedHarmonic p` (type I) or
`alternatingGeneralizedHarmonic p` (types II, III), `ζ(q) = ∑ 1/n^q`, and `ζ̄ =
alternatingZeta`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 17 (`jis-2024-24.4.1-thm-17`). -/
public theorem_wanted sum_primes_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    {α m p q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hp : 1 ≤ p) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pr : ℕ → ℕ := fun l => Nat.nth Nat.Prime (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((α + m * y + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pr l ≤ x),
        (pr l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m * (x : ℝ) ^ (α + m * (y - 1) + 1) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((α + m * (y - 1) + 1 : ℕ) : ℝ) *
          Real.log x ^ (m * (y - 1) + 1)))

/-- Theorem 18: the analogues of Theorem 17 with `p_ℓ` replaced by `p_{ℓ,k}` (`k ≥ 1`). Corrected
reading: the first two items print `H_ℓ^{(p,2y+1,1)}` (type I), but their asymptotics carry
`ζ̄(p)`, the section treats type III, and the proof sums `H_ℓ^{(p,2y+1,3)}`; they are read
with type III. Sums run over `ℓ ≤ x` (`ℓ ∈ [1, x]`) or over `p_ℓ ≤ x` for natural `x → ∞` (the
sums depend on `⌊x⌋` only); `p_ℓ = Nat.nth Nat.Prime (ℓ - 1)`, `p_{ℓ,k}` is the `ℓ`th
squarefree number with exactly `k` prime factors, `H_n^{(p,r,i)}` is `signedIteratedPartialSum` over
`generalizedHarmonic p` (type I) or `alternatingGeneralizedHarmonic p` (types II, III), `ζ(q)
= ∑ 1/n^q`, and `ζ̄ = alternatingZeta`.

Source: Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024),
Article 24.4.1, Theorem 18 (`jis-2024-24.4.1-thm-18`). -/
public theorem_wanted sum_squarefreeKPrime_pow_mul_alternatingHyperharmonic_typeIII_isEquivalent
    {α m k p q y : ℕ}
    (hα : 1 ≤ α) (hm : 1 ≤ m) (hk : 1 ≤ k) (hp : 1 ≤ p) (hy : 1 ≤ y) (hq : 2 ≤ q) :
    let pk : ℕ → ℕ := fun l =>
      Nat.nth (fun t => Squarefree t ∧ t.primeFactors.card = k) (l - 1)
    let ζq : ℝ := ∑' i : ℕ, 1 / (i : ℝ) ^ q
    let HIII := fun (s : ℝ) (r n : ℕ) =>
      signedIteratedPartialSum true (alternatingGeneralizedHarmonic s) r n
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * alternatingZeta p ^ m *
        (x : ℝ) ^ (α + m * y + 1) * Real.log x ^ (α) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII p (2 * y + 1) l) ^ m) ~[atTop]
      fun x : ℕ => alternatingZeta p ^ m * (x : ℝ) ^ (α + m * y + 1) *
        Real.log (Real.log x) ^ ((m * y + 1) * (k - 1)) /
        (((2 ^ y * y.factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * y + 1) *
          ((α + m * y + 1 : ℕ) : ℝ) * Real.log x ^ (m * y + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log x ^ (α + m) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII 1 (2 * y) l) ^ m) ~[atTop]
      fun x : ℕ => (x : ℝ) ^ (α + m * (y - 1) + 1) *
        Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 ^ y * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
            ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ ((m : ℤ) * ((y : ℤ) - 2) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l - 1)) ^ m) ~[atTop]
      fun x : ℕ => (ζq + alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1))) ∧
    ((fun x : ℕ => ∑ l ∈ Icc 1 x,
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => ((k - 1).factorial : ℝ) ^ α * (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log x ^ (α) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log (Real.log x) ^ (α * (k - 1)))) ∧
    ((fun x : ℕ => ∑ l ∈ (Icc 1 x).filter (fun l => pk l ≤ x),
        (pk l : ℝ) ^ α * (HIII q (2 * y) (2 * l)) ^ m) ~[atTop]
      fun x : ℕ => (ζq - alternatingZeta q) ^ m *
        (x : ℝ) ^ (α + m * (y - 1) + 1) * Real.log (Real.log x) ^ ((m * (y - 1) + 1) * (k - 1)) /
        (((2 * (y - 1).factorial : ℕ) : ℝ) ^ m * ((k - 1).factorial : ℝ) ^ (m * (y - 1) + 1) *
          ((α + m * (y - 1) + 1 : ℕ) : ℝ) * Real.log x ^ (m * (y - 1) + 1)))


end

end MetaMathlibExt
