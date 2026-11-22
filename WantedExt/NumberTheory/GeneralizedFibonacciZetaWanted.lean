/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter
open scoped BigOperators Topology

/-!
# The ℓ-generalized Fibonacci zeta function

Statement-only formalizations of the principal results in Meher and Sahoo's paper.
The generalized Fibonacci sequence is represented by a quantified integer-indexed
function satisfying its initial window and recurrence, rather than by a new recursive
definition.
-/

/-- `IsLGeneralizedFibonacci ℓ F` says that `F : ℤ → ℤ` has the paper's zero initial
window from `2 - ℓ` through `0`, has `F 1 = 1`, and satisfies the ℓ-step recurrence
at every index greater than one.  Values below `2 - ℓ` are deliberately unconstrained,
because the paper defines the sequence only from that index onward.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Definition
preceding Proposition 1. -/
public def IsLGeneralizedFibonacci (ℓ : ℕ) (F : ℤ → ℤ) : Prop :=
  (∀ n : ℤ, 2 - (ℓ : ℤ) ≤ n → n < 1 → F n = 0) ∧
    F 1 = 1 ∧
    ∀ n : ℤ, 1 < n →
      F n = ∑ i ∈ Finset.range ℓ, F (n - 1 - (i : ℤ))

/-- The characteristic polynomial `φ_ℓ(X) = X^ℓ - ∑_{i < ℓ} X^i`, which is the
paper's `X^ℓ - X^(ℓ-1) - ⋯ - X - 1`, over `ℂ`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Characteristic polynomial definition. -/
public noncomputable def lGeneralizedFibonacciCharacteristic (ℓ : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ ℓ - ∑ i ∈ Finset.range ℓ, Polynomial.X ^ i

/-- The Dresden--Du coefficient `c(β) = (β - 1) / (2 + (ℓ + 1)(β - 2))`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Coefficient definition preceding Lemma 1. -/
public noncomputable def lGeneralizedFibonacciCoefficient (ℓ : ℕ) (β : ℂ) : ℂ :=
  (β - 1) / (2 + ((ℓ : ℂ) + 1) * (β - 2))

/-- The finset of roots of `φ_ℓ` other than the distinguished real root `α`.
Multiplicity is intentionally discarded with `toFinset`, as requested: the paper's
roots are simple, but simplicity is not reproved in this statement-only formalization.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85,
Root notation preceding Proposition 1. -/
public noncomputable def lGeneralizedFibonacciOtherRoots (ℓ : ℕ) (α : ℝ) : Finset ℂ :=
  ((lGeneralizedFibonacciCharacteristic ℓ).roots.toFinset).erase (α : ℂ)

/-- The possible pole indexed by the exponent tuple `κ` and integer `n`.  The natural
number called `k` in the paper is represented by the sum of `κ` over the non-dominant
roots.  Only the values of the unrestricted function `κ : ℂ → ℕ` on that finite root
set enter this definition.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPole
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  -((∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ β : ℕ) : ℂ) +
    (2 * (n : ℂ) * (Real.pi : ℂ) * Complex.I +
        ∑ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, (κ β : ℂ) * Complex.log β) /
      Complex.log (α : ℂ)

/-- For `ℓ = 2` the characteristic polynomial is the Fibonacci polynomial `X² - X - 1`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Equation (3). -/
public theorem lGeneralizedFibonacciCharacteristic_two :
    lGeneralizedFibonacciCharacteristic 2 = Polynomial.X ^ 2 - Polynomial.X - 1 := by
  simp [lGeneralizedFibonacciCharacteristic, Finset.sum_range_succ]
  ring

/-- The index `κ = 0`, `n = 0` gives the possible pole `s = 0`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem lGeneralizedFibonacciZetaPole_zero (ℓ : ℕ) (α : ℝ) :
    lGeneralizedFibonacciZetaPole ℓ α (fun _ => 0) 0 = 0 := by
  simp [lGeneralizedFibonacciZetaPole]

/-- The set `S` of all possible poles from Theorem 1.  Exponent functions which agree
on the non-dominant-root finset describe the same tuple; values elsewhere are ignored.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaPoleSet (ℓ : ℕ) (α : ℝ) : Set ℂ :=
  {s | ∃ (κ : ℂ → ℕ) (n : ℤ), s = lGeneralizedFibonacciZetaPole ℓ α κ n}

/-- The residue expression in Theorem 1, with `k = ∑ κ(β)`.  `Ring.choose` encodes
the generalized binomial coefficient, the factorial quotient encodes the multinomial
coefficient, natural powers encode the product over non-dominant roots, and complex
powers encode the two generally nonintegral exponents.  As in the paper, all logarithms
are principal `Complex.log` values.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public noncomputable def lGeneralizedFibonacciZetaResidue
    (ℓ : ℕ) (α : ℝ) (κ : ℂ → ℕ) (n : ℤ) : ℂ :=
  let roots := lGeneralizedFibonacciOtherRoots ℓ α
  let k := (∑ β ∈ roots, κ β)
  let s₀ := lGeneralizedFibonacciZetaPole ℓ α κ n
  let dominant :=
    lGeneralizedFibonacciCoefficient ℓ (α : ℂ) * (α : ℂ)⁻¹
  dominant ^ (-s₀) *
    Ring.choose (-s₀) k *
    dominant ^ (-(k : ℂ)) *
    ((Nat.factorial k : ℂ) /
      ∏ β ∈ roots, (Nat.factorial (κ β) : ℂ)) *
    (∏ β ∈ roots,
      (lGeneralizedFibonacciCoefficient ℓ β * β⁻¹) ^ κ β) *
    (1 / Complex.log (α : ℂ))

/-- The point printed in Corollary 1.  The even branch is
`-(k + k/(ℓ-1)) + iπ(2n + k/(ℓ-1))/log α`; the odd branch is
`-(k + k/(ℓ-1)) + i2nπ/log α`.  Natural division is legitimate under the
corollary's divisibility hypothesis.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public noncomputable def lGeneralizedFibonacciZetaCorollaryPole
    (ℓ k : ℕ) (α : ℝ) (n : ℤ) : ℂ :=
  -((k + k / (ℓ - 1) : ℕ) : ℂ) +
    if Even ℓ then
      Complex.I * (Real.pi : ℂ) *
          ((2 * n + (k / (ℓ - 1) : ℕ) : ℤ) : ℂ) /
        Complex.log (α : ℂ)
    else
      Complex.I * (2 * (n : ℂ) * (Real.pi : ℂ)) /
        Complex.log (α : ℂ)

/-- Proposition 1: for an ℓ-generalized Fibonacci sequence with `ℓ ≥ 2`, the series
of norms of `(F_n)^{-s}` is summable whenever `Re(s) > 0`.  Reindexing by `j ↦ j+1`
expresses the paper's indices `n ≥ 1` as a Lean sum over `j : ℕ`; the complex power is
`Complex.cpow` through `HPow ℂ ℂ`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Proposition 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_summable
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (s : ℂ) (hs : 0 < s.re) :
    Summable (fun j : ℕ => ‖((F ((j : ℤ) + 1) : ℂ) ^ (-s))‖)

/-- Theorem 1, continuation and possible-pole clauses: there is a function agreeing
with the defining zeta series on `Re(s) > 0`, differentiable away from the explicitly
defined set `S`, and having a finite punctured limit of `(s-s₀)f(s)` at every point of
`S`.  The last clause formalizes “at most simple poles”; the residue value is separated
into `lGeneralizedFibonacciZeta_residue` so collision handling can be stated explicitly.
The real root `α` is hypothesis-characterized by `1 < α` and its characteristic
equation, while irreducibility, uniqueness outside the unit circle, and root simplicity
are not reproved or added as redundant hypotheses.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_meromorphicContinuation
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i) :
    ∃ f : ℂ → ℂ,
      (∀ s : ℂ, 0 < s.re →
        f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
        DifferentiableAt ℂ f s) ∧
      ∀ s₀ : ℂ, s₀ ∈ lGeneralizedFibonacciZetaPoleSet ℓ α →
        ∃ r : ℂ,
          Tendsto (fun s : ℂ => (s - s₀) * f s) (𝓝[≠] s₀) (𝓝 r)

/-- The residue clause of Theorem 1: if `(κ,n)` is the unique pole index modulo
equality of exponent values on the non-dominant-root finset, then every continuation
which agrees with the series on the right half-plane and is differentiable off `S`
has the stated punctured residue limit.  The uniqueness hypothesis is an explicit
deviation from the paper: when different tuples collide, their residue contributions
must be added, a case the printed formula does not address.  Equality deliberately
does not compare `κ` away from the finite root set.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 1
(residue formula). -/
public theorem_wanted lGeneralizedFibonacciZeta_residue
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (κ : ℂ → ℕ) (n : ℤ)
    (hunique : ∀ (κ' : ℂ → ℕ) (n' : ℤ),
      lGeneralizedFibonacciZetaPole ℓ α κ' n' =
          lGeneralizedFibonacciZetaPole ℓ α κ n →
        n' = n ∧
          ∀ β ∈ lGeneralizedFibonacciOtherRoots ℓ α, κ' β = κ β)
    (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s) :
    Tendsto
      (fun s : ℂ =>
        (s - lGeneralizedFibonacciZetaPole ℓ α κ n) * f s)
      (𝓝[≠] lGeneralizedFibonacciZetaPole ℓ α κ n)
      (𝓝 (lGeneralizedFibonacciZetaResidue ℓ α κ n))

/-- Corollary 1: if `(ℓ-1) ∣ k`, then for every integer `n` the point printed by the
paper (using its even/odd alternatives) belongs to the possible-pole set `S` of
Theorem 1.  In the witnessing tuple `κ` is constant `k/(ℓ-1)` on all
non-dominant roots in the witnessing tuple.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Corollary 1. -/
public theorem_wanted lGeneralizedFibonacciZeta_corollaryPole_mem
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (k : ℕ) (hk : ℓ - 1 ∣ k) (n : ℤ) :
    lGeneralizedFibonacciZetaCorollaryPole ℓ k α n ∈
      lGeneralizedFibonacciZetaPoleSet ℓ α

/-- Theorem 2: at a positive integer `m`, any continuation agreeing with the zeta
series on the right half-plane and differentiable away from `S` takes a rational value
at `-m`, provided it is differentiable there.  The final differentiability hypothesis
is the formal “`-m` is not a pole” premise, and rationality is expressed by equality
with the complex coercion of some `q : ℚ`.

Source: Nabin Kumar Meher and Dilip Kumar Sahoo, *Analytic Continuation of the
ℓ-Generalized Fibonacci Zeta Function*, INTEGERS 24 (2024), Article A85, Theorem 2. -/
public theorem_wanted lGeneralizedFibonacciZeta_negInt_rational
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (F : ℤ → ℤ)
    (hF : IsLGeneralizedFibonacci ℓ F) (α : ℝ) (hα : 1 < α)
    (hαroot : α ^ ℓ = ∑ i ∈ Finset.range ℓ, α ^ i)
    (m : ℕ) (hm : 0 < m) (f : ℂ → ℂ)
    (hseries : ∀ s : ℂ, 0 < s.re →
      f s = ∑' j : ℕ, ((F ((j : ℤ) + 1) : ℂ) ^ (-s)))
    (hregular : ∀ s : ℂ, s ∉ lGeneralizedFibonacciZetaPoleSet ℓ α →
      DifferentiableAt ℂ f s)
    (hmregular : DifferentiableAt ℂ f (-(m : ℂ))) :
    ∃ q : ℚ, f (-(m : ℂ)) = (q : ℂ)

end

end MetaMathlibExt
