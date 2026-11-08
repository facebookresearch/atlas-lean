/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Algebraic integers with conjugates in a prescribed distribution

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.AlgebraicIntegers` — annals_algebraic_integers (manifest `manifests/problems/annals_algebraic_integers.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.AlgebraicIntegersWanted` namespace. Mathematical
statements are unchanged. Source: A. Smith, `Algebraic integers with conjugates in a prescribed distribution`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-AlgebraicIntegers.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.AlgebraicIntegersWanted
/-!
# Main Statement from Algebraic integers with conjugates in a prescribed distribution

We formalise the statement of the main result from A. Smith,
`Algebraic integers with conjugates in a prescribed distribution`, Annals of Math, 200 (1) 2024.
-/

set_option autoImplicit false

namespace AlgebraicIntegers

open ComplexOrder

/-- The trace of an algebraic integer `α ∈ ℂ` is the sum `α₁ + ... + αₙ`, where
`αᵢ` are the complex roots of the minimal polynomial of `α` over `ℚ`. -/
noncomputable def trace (α : ℂ) : ℂ := ((minpoly ℚ α).aroots ℂ).sum

/-- The degree of an algebraic integer is the degree of the minimal polynomial
of `α` over `ℚ`. -/
noncomputable def degree (α : ℂ) : ℕ := (minpoly ℚ α).natDegree

/-- We call an algebraic number `α` totally positive if its conjugates `α₁, ..., αₙ` are all
positive real numbers.

Note that `open ComplexOrder` gives the complex numbers a partial ordering, with `x < y` defined to
mean that `y - x` is a positive real number. -/
def IsTotallyPositive (α : ℂ) : Prop :=
  IsAlgebraic ℚ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, 0 < β

/-- Take `λ_SSS` to be the greatest real number `λ` such that, for any `ε > 0`,
there are only finitely many totally positive algebraic integers α satisfying
`tr(α) < (λ − ε) * deg(α)`. Note that the paper said "least real number",
but this is clearly a typo, as this set does not have a lower bound. Defining
it as the greatest real number is consistent with how this constant is defined in
another paper by the same author, namely in Orloski, Sardari and Smith: "New
lower bounds for the Schur-Siegel-Smyth trace problem" (arXiv:2401.03252).
There, `λ_SSS` is defined as the limit inferior of `tr(α)/deg(α)` over all
totally positive `α`, which is exactly the *greatest* real number `λ` such that
for all `ε > 0`, only finitely many `α` have `tr(α)/deg(α) < λ - ε`. -/
noncomputable def lambda_SSS : ℝ := sSup { lam : ℝ | ∀ ε > (0 : ℝ),
  { α : ℂ | IsIntegral ℤ α ∧ IsTotallyPositive α ∧ trace α < (lam - ε) * degree α }.Finite }

/--
Statement of Theorem 1.1:

We have `λ_SSS < 1.89831`.
Source: A. Smith, `Algebraic integers with conjugates in a prescribed distribution`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-AlgebraicIntegers.lean Via leanprover/lean-eval@38361be, problem `annals_algebraic_integers`.
-/
public theorem_wanted theorem_1_1 : lambda_SSS < 1.89831

end AlgebraicIntegers

end MathlibExt.NumberTheory.AlgebraicIntegersWanted
