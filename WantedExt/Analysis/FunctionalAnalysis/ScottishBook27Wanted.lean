/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted

/-- A function `F : E → ℂ` on a complex Banach space is a (continuous) polynomial
function if it is a finite sum of homogeneous terms, each given by a continuous
multilinear map applied diagonally. -/
def IsPolynomialOn (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) : Prop :=
  ∃ (n : ℕ) (m : Fin n → ℕ)
    (A : (i : Fin n) → (E [× m i]→L[ℂ] ℂ)),
    ∀ x, F x = ∑ i, A i fun _ => x

/--
Mazur-Orlicz, Problem 27 of the Scottish Book. Original question: if complex
polynomials `F, G` on a complex space of type (B) both tend to `0` along a
sequence `x_n` in the unit ball, is there a common zero `x₀` with
`F x₀ = 0` and `G x₀ = 0`? The answer is positive. This file formalizes the
contrapositive Bezout identity recorded in the addendum in the Scottish Book
(Mazur-Orlicz, 4 April 1939): if `F` and `G` have no common zero, there are
complex polynomials `φ, ψ` with `F φ + G ψ = 1` throughout `E`. The original
question follows from this by contradiction: along the sequence `x_n` both
`F x_n` and `G x_n` tend to `0`, while `F x_n * φ x_n + G x_n * ψ x_n = 1`.
Source: S. Mazur and W. Orlicz, Problem 27 of the Scottish Book, with the
positive answer via the Bezout identity in the addendum; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted bezout_identity_for_polynomials_without_common_zero :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (F G : E → ℂ),
      IsPolynomialOn E F → IsPolynomialOn E G →
      (∀ x, F x = 0 → G x ≠ 0) →
      ∃ (φ ψ : E → ℂ), IsPolynomialOn E φ ∧ IsPolynomialOn E ψ ∧
        ∀ x, F x * φ x + G x * ψ x = 1

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook27Wanted
