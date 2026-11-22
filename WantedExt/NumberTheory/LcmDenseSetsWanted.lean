/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Order.Filter.AtTopBot.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter


/-- The paper's truncated logarithm `Log x = max (log x) 1`, made total on all real
inputs although the paper uses it for positive inputs.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog (x : ℝ) : ℝ :=
  max (Real.log x) 1

/-- The paper's second iterated truncated logarithm `Log₂ x = Log (Log x)`.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog2 (x : ℝ) : ℝ :=
  truncLog (truncLog x)

/-- The paper's third iterated truncated logarithm `Log₃ x = Log (Log₂ x)`.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog3 (x : ℝ) : ℝ :=
  truncLog (truncLog2 x)

/-- The truncated logarithm is always at least one; this records the effect of the
`max` in the paper's definition.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public theorem one_le_truncLog (x : ℝ) : 1 ≤ truncLog x := by
  exact le_max_right _ _

/-- The finite set encoding the paper's positive integers `n ∈ A` with `n ≤ x`.
The upper endpoint is `⌊x⌋₊`, so the definition is total even for negative `x`.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def naturalsInSetUpTo (A : Set ℕ) (x : ℝ) : Finset ℕ :=
  open Classical in (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ A)

/-- No positive integer in the empty set occurs in the finite summation range.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem naturalsInSetUpTo_empty (x : ℝ) :
    naturalsInSetUpTo ∅ x = ∅ := by
  simp [naturalsInSetUpTo]

/-- The finite harmonic sum `∑_{n ∈ A, n ≤ x} 1 / n`; the range begins at one,
matching the paper's convention that natural numbers are positive.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def recipSumUpTo (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x, 1 / (n : ℝ)

/-- The harmonic sum of the empty set is zero.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem recipSumUpTo_empty (x : ℝ) : recipSumUpTo ∅ x = 0 := by
  simp [recipSumUpTo]

/-- The paper's double sum `∑_{n,m ∈ A, n,m ≤ x} 1 / lcm(n,m)`, with all
natural-number quantities explicitly coerced to real numbers.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
public noncomputable def lcmReciprocalSum (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x, 1 / (Nat.lcm n m : ℝ)

/-- The double least-common-multiple sum of the empty set is zero.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
@[simp] public theorem lcmReciprocalSum_empty (x : ℝ) : lcmReciprocalSum ∅ x = 0 := by
  simp [lcmReciprocalSum]

/-- The numerator of the logarithmic expectation of `gcd(n,m)`: expanding the
two independent logarithmic weights gives `∑ gcd(n,m)/(n*m)` over the finite range.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def gcdLogarithmicMoment (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x,
      (Nat.gcd n m : ℝ) / ((n : ℝ) * (m : ℝ))

/-- The defect `E gcd(n,m) - 1` from equation (9), written as the quotient of
the expanded gcd moment by the square of the harmonic sum, minus one. If the
finite range is empty, Lean's division by zero makes this value `-1`; the main
statements use the definition only eventually, or have a zero harmonic left side.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def lcmDefect (A : Set ℕ) (x : ℝ) : ℝ :=
  gcdLogarithmicMoment A x / recipSumUpTo A x ^ 2 - 1

/-- On the empty set the defect is `-1`, as dictated by Lean's total division.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
@[simp] public theorem lcmDefect_empty (x : ℝ) : lcmDefect ∅ x = -1 := by
  simp [lcmDefect, gcdLogarithmicMoment]

/-- `primeProductLayer 𝒫 k` is the paper's `𝒫^[k]`: the products of exactly `k`
distinct primes from `𝒫`. In particular, the squarefree number `1` belongs exactly
to the zero layer because its set of prime factors is empty.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductLayer (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | Squarefree n ∧
    (∀ p, p.Prime → p ∣ n → p ∈ P) ∧
    n.primeFactors.card = k}

/-- `primeProductsAtMost 𝒫 k` is the paper's `𝒫^[≤k]`, encoded by membership in
some exact layer indexed by `j ≤ k` rather than by an explicit set union.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductsAtMost (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ j ≤ k, n ∈ primeProductLayer P j}

/-- The at-most-zero prime-product layer is the exact zero layer, a characteristic
fact about the existential encoding of `𝒫^[≤k]`.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public theorem primeProductsAtMost_zero (P : Set ℕ) :
    primeProductsAtMost P 0 = primeProductLayer P 0 := by
  ext n
  simp [primeProductsAtMost]

/-- The growth function `F` of equations (13)--(15). It takes
`k = ⌈C₀ * sqrt(Log₂ x)⌉ - 1`, using truncated natural subtraction; sets
`h(x) = Log₂ x - k²/C₀² + 1`; evaluates the same formula at
`x_(k+1) = exp(exp((k+1)²/C₀²))`; sets `ψ(x) = 1 + h(x)²/h(x_(k+1))`;
and returns `ψ(x) * k^(2k) * C₀^(-2k) / k!`. The final negative power is
encoded by division by `C₀^(2k)`. This total definition is used by the theorem
only for positive `C₀` and sufficiently large `x`, as in the paper.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equations (13)--(15).
-/
public noncomputable def lcmDenseGrowthF (C₀ x : ℝ) : ℝ :=
  let k : ℕ := Nat.ceil (C₀ * Real.sqrt (truncLog2 x)) - 1
  let h : ℝ := truncLog2 x - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let xNext : ℝ := Real.exp (Real.exp (((k + 1 : ℕ) : ℝ) ^ 2 / C₀ ^ 2))
  let hNext : ℝ := truncLog2 xNext - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let ψ : ℝ := 1 + h ^ 2 / hNext
  ψ * (k : ℝ) ^ (2 * k) / C₀ ^ (2 * k) / (k.factorial : ℝ)

/-- Lemma 1 (logarithmic growth rate). The absolute positive constants `c` and
`C` precede `𝒫`, `k`, and `x`. Assuming every member of `𝒫` is prime, `x ≥ 1`,
and `k ≤ c*S`, the four inequalities state that both the exact-`k` and at-most-`k`
harmonic sums are comparable to `S^k/k!`. The paper's `k ≥ 0` is automatic for
`k : ℕ`; `𝒫^[k]` and `𝒫^[≤k]` use the squarefree-layer definitions above.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1.
-/
public theorem_wanted recipSum_primeProductLayer_asymp :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Set ℕ) (k : ℕ) (x : ℝ),
      (∀ p ∈ P, p.Prime) →
      1 ≤ x →
      let S := recipSumUpTo P x
      let Tk := recipSumUpTo (primeProductLayer P k) x
      let Tle := recipSumUpTo (primeProductsAtMost P k) x
      (k : ℝ) ≤ c * S →
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tk ∧
        Tk ≤ C * (S ^ k / (k.factorial : ℝ)) ∧
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tle ∧
        Tle ≤ C * (S ^ k / (k.factorial : ℝ))

/-- Theorem 1 (negative answer to Erdős problem #442), existence portion. For
every positive `C₀`, there is a set `A` (all sums run over `1 ≤ n ≤ x`, so whether
`0 ∈ A` is irrelevant); an error `e(x) → 0` gives the eventual equality (11); and a
positive `C₀`-dependent constant `K` gives the eventual LCM-sum bound (12). The informal
optimality sentence is omitted because its precise formal content is delegated to Theorem 2(ii).
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 1.
-/
public theorem_wanted exists_dense_set_large_lcm :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            recipSumUpTo A x =
              Real.exp ((C₀ / 2 + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmReciprocalSum A x ≤ K * recipSumUpTo A x ^ 2

/-- Theorem 2(i), construction with controlled defect. A single absolute positive
constant `C` works for every positive `C₀`. The resulting set (sums over
`1 ≤ n ≤ x`) has its harmonic sum eventually within a positive factor `K` of
`lcmDenseGrowthF C₀ x`, and an error `e(x) → 0` gives the eventual equation-(21) defect bound
`≪ exp(e² C₀²) - 1 + o(1)` as printed in the journal version (the arXiv v1 TeX prints
`exp(C₀²)`; its proof, through the factor `e^ℓ` of (35), gives `e² C₀²`). The
dependence of `K` and `e` on `C₀` is represented by choosing them after `C₀`.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(i).
-/
public theorem_wanted exists_dense_set_controlled_defect :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmDenseGrowthF C₀ x / K ≤ recipSumUpTo A x ∧
            recipSumUpTo A x ≤ K * lcmDenseGrowthF C₀ x) ∧
        ∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            lcmDefect A x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + e x)

/-- Proposition 1 (baby version of Theorem 2(i)'s construction; the paper's lead-in
sentence says Theorem 2(ii), but the construction and estimates (31), (21) are those of
part (i)). There is an absolute
`C > 0` such that for every `C₀ > 0` there are sets `A_k` (depending on `k` and `C₀`) for
which (31), `∑_{n ∈ A_k, n ≤ x} 1/n = exp((C₀/2 + o(1)) Log₂^{1/2} x Log₃ x)`, and (21),
`E gcd(n, m) - 1 ≤ C (exp(e² C₀²) - 1 + o(1))`, hold in the range (32),
`C₀ Log₂^{1/2} x = (1 + o(1)) k`, all `o(1)` as `k → ∞`. The nested `o(1)` are written in
`ε`-`δ` form: for every `ε > 0` there are `δ > 0` and `k₀` such that for `k ≥ k₀` and every `x`
with `|C₀ Log₂^{1/2} x - k| ≤ δ k` both errors are at most `ε`; `A` is chosen before `ε`.
The constant of `≪` in (21) is absolute, as in Theorem 2(i).
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Proposition 1, (31) and (32), with (21)
(`integers-2024-A100-prop-1`).
-/
public theorem_wanted exists_dense_sets_baby :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : ℕ → Set ℕ,
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : ℝ,
            |C₀ * truncLog2 x ^ (1 / 2 : ℝ) - k| ≤ δ * k →
              (∃ e : ℝ, |e| ≤ ε ∧
                recipSumUpTo (A k) x =
                  Real.exp ((C₀ / 2 + e) * truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
              lcmDefect (A k) x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + ε)

/-- Theorem 2(ii), the uniform converse bound. For each positive `C₀`, the error
function `e(x) → 0` is chosen before `x` and before the set `A`, so the `o(1)` is
uniform in `A`. Eventually, every set `A ⊆ ℕ` (sums over `1 ≤ n ≤ x`) whose defect at that `x`
is at most `C₀²` obeys (23). An empty finite range is harmless because its
harmonic sum, the left side of the conclusion, is zero.
Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(ii).
-/
public theorem_wanted uniform_harmonic_bound_of_defect :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ e : ℝ → ℝ,
        Tendsto e atTop (nhds 0) ∧
        ∀ᶠ x in atTop,
          ∀ A : Set ℕ,
            lcmDefect A x ≤ C₀ ^ 2 →
            recipSumUpTo A x ≤
              Real.exp ((C₀ + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)

end

end MetaMathlibExt
