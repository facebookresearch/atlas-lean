/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.ScottishBook74Wanted

/-- Evaluation of the homogeneous polynomial with coefficient function
`a` at `t`, summing over exponent multi-indices of total degree `n`.
Source: Scottish Book Problem 74. -/
def EvalPoly (n : ℕ) (a : (Fin n → ℕ) → ℝ) (t : Fin n → ℝ) : ℝ :=
  ∑ k ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
      (fun k => ∑ i, k i = n),
    a k * ∏ i, t i ^ k i

/-- Scottish Book Problem 74, resolved upper bound: if a homogeneous
polynomial of degree `n` is bounded by `1` on the ℓ¹ unit ball, then
every coefficient satisfies `|a_k| ≤ nⁿ / (k₁! ⋯ kₙ!)`. This is the
upper-bound part of Problem 74 only; the open best-constant question
is not formalized here (see `scottishBook74_holds`). -/
def ScottishBookProblem74Claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ a : (Fin n → ℕ) → ℝ,
      (∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ 1 → |EvalPoly n a t| ≤ 1) →
      ∀ k : Fin n → ℕ, (∑ i, k i) = n →
        |a k| ≤ (n : ℝ) ^ n / ∏ i, (Nat.factorial (k i) : ℝ)

/--
The resolved upper bound of Scottish Book Problem 74 holds
(solved-positive). Source: S. Mazur and W. Orlicz, Problem 74 of the
Scottish Book; typescript PDF p.36, printed p.33; see the commentary
in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
Proved by the classical polarization identity; the Rademacher form
is Lemma 12 of M. Chatzakou and Y. Sarantopoulos, "Estimates for
polynomial norms on Banach spaces", arXiv:2107.05993. Sketch: let `P`
be `n`-homogeneous with `|P(t)| ≤ 1` for `‖t‖₁ ≤ 1`, and let `L` be
its symmetric `n`-linear polar form. Polarization gives
`L(x₁, …, xₙ) = (1/(2ⁿ n!)) Σ_{ε ∈ {±1}ⁿ} ε₁⋯εₙ P(Σᵢ εᵢ xᵢ)`.
Take the multiset `x₁, …, xₙ` to be `e₁` with multiplicity `k₁`,
…, `eₙ` with multiplicity `kₙ`, so `Σ kᵢ = n`. Then
`a_k = (n! / ∏ kᵢ!) · L(e₁^{k₁}, …, eₙ^{kₙ})`, and
`‖Σᵢ εᵢ xᵢ‖₁ ≤ Σⱼ kⱼ = n`, so by homogeneity
`|P(Σᵢ εᵢ xᵢ)| ≤ nⁿ`. Hence
`|L(e₁^{k₁}, …, eₙ^{kₙ})| ≤ (1/(2ⁿ n!)) · 2ⁿ · nⁿ = nⁿ / n!`, and
`|a_k| ≤ (n! / ∏ kᵢ!) · (nⁿ / n!) = nⁿ / ∏ kᵢ!`.
The genuinely open content of Problem 74, the exact best constant
`C*(n, k) = sup { |a_k| : ‖P‖ ≤ 1 }`, is NOT formalized in Lean:
no closed form for `C*` is known. In particular the bound filed
here is not sharp for all `k`: for `k = (n, 0, …, 0)` with `n ≥ 2`,
the best constant is `1` (since `|a_k| = |P(e₁)| ≤ 1`) while the
bound is `nⁿ / n! > 1`. So no sharpness, attainment, or `IsLeast`
clause with the constant `nⁿ / ∏ kᵢ!` may be added (it would be
false), and a bare `∃ C, IsLeast …` clause would be resolved-true
and formalize nothing open. The monomial gives the lower bound
`C*(n, k) ≥ nⁿ / ∏ kᵢ^{kᵢ}` (with `0^0 := 1`).
-/
theorem_wanted scottishBook74_holds : ScottishBookProblem74Claim

end MathlibExt.Analysis.ScottishBook74Wanted
