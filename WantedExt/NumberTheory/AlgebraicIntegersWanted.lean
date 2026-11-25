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

/-- **Sum of the conjugates of a complex number.** For a complex number $\alpha$, the trace
$\operatorname{tr}(\alpha) \in \mathbb{C}$ is the sum, counted with multiplicity, of the complex
roots of the minimal polynomial of $\alpha$ over $\mathbb{Q}$. When $\alpha$ is algebraic these
roots are the conjugates $\alpha_1, \dots, \alpha_n$ of $\alpha$, so
$\operatorname{tr}(\alpha) = \alpha_1 + \dots + \alpha_n$; when $\alpha$ is transcendental its
minimal polynomial is $0$ by convention and $\operatorname{tr}(\alpha) = 0$. -/
noncomputable def trace (α : ℂ) : ℂ := ((minpoly ℚ α).aroots ℂ).sum

/-- **Degree of a complex number over the rationals.** For a complex number $\alpha$, the degree
$\deg(\alpha)$ is the natural number given by the degree of the minimal polynomial of $\alpha$ over
$\mathbb{Q}$. When $\alpha$ is transcendental its minimal polynomial is $0$ by convention, so
$\deg(\alpha) = 0$. -/
noncomputable def degree (α : ℂ) : ℕ := (minpoly ℚ α).natDegree

/-- **Totally positive algebraic numbers.** A complex number $\alpha$ is totally positive if it is
algebraic over $\mathbb{Q}$ and every complex root of its minimal polynomial over $\mathbb{Q}$,
that is, every conjugate of $\alpha$, is a positive real number. -/
def IsTotallyPositive (α : ℂ) : Prop :=
  IsAlgebraic ℚ α ∧ ∀ β ∈ (minpoly ℚ α).aroots ℂ, 0 < β

/-- **The Schur–Siegel–Smyth constant $\lambda_{\mathrm{SSS}}$.** Let $\lambda_{\mathrm{SSS}}$ be
the supremum in $\mathbb{R}$ of the set of real numbers $\lambda$ such that, for every
$\varepsilon > 0$, only finitely many complex numbers $\alpha$ are totally positive algebraic
integers with $\operatorname{tr}(\alpha) < (\lambda - \varepsilon) \deg(\alpha)$, where
$\operatorname{tr}(\alpha)$ and $\deg(\alpha)$ are the trace and the degree of $\alpha$ over
$\mathbb{Q}$ (the trace of a totally positive $\alpha$ is real). By the convention for suprema in
$\mathbb{R}$, $\lambda_{\mathrm{SSS}} = 0$ if this set is empty or unbounded above.

The set is closed downwards and contains its supremum when it is nonempty and bounded above, so
$\lambda_{\mathrm{SSS}}$ is then the greatest such $\lambda$. The source says "least real number",
but this is a typo, as the set has no lower bound. The greatest real number agrees with Orloski,
Sardari and Smith, "New lower bounds for the Schur-Siegel-Smyth trace problem"
(arXiv:2401.03252), where $\lambda_{\mathrm{SSS}}$ is the limit inferior of
$\operatorname{tr}(\alpha)/\deg(\alpha)$ over all totally positive algebraic integers $\alpha$. -/
noncomputable def lambda_SSS : ℝ := sSup { lam : ℝ | ∀ ε > (0 : ℝ),
  { α : ℂ | IsIntegral ℤ α ∧ IsTotallyPositive α ∧ trace α < (lam - ε) * degree α }.Finite }

/--
**Smith's theorem on the Schur–Siegel–Smyth trace problem.** The Schur–Siegel–Smyth constant
satisfies $\lambda_{\mathrm{SSS}} < 1.89831$; this is Theorem 1.1 of the source.

Source: A. Smith, `Algebraic integers with conjugates in a prescribed distribution`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-AlgebraicIntegers.lean Via leanprover/lean-eval@38361be, problem `annals_algebraic_integers`.
-/
public theorem_wanted theorem_1_1 : lambda_SSS < 1.89831

end AlgebraicIntegers

end MathlibExt.NumberTheory.AlgebraicIntegersWanted
