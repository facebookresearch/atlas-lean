/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flat Littlewood polynomials exist

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FlatLittlewoodPoly` — annals_flat_littlewood_poly (manifest `manifests/problems/annals_flat_littlewood_poly.toml`, rev 1, submitter Katerina Hristova, Kevin Buzzard, Bhavik Mehta, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FlatLittlewoodPolyWanted` namespace. Mathematical
statements are unchanged. Source: P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, and M. Tiba, `Flat Littlewood polynomials exist`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-FlatLittlewoodPoly.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace MathlibExt.Analysis.FlatLittlewoodPolyWanted
/-!
# Main Statement from Flat Littlewood polynomials exist

We formalise the statement of the main result from P. Balister, B. Bollobás, R. Morris,
J. Sahasrabudhe, and M. Tiba, `Flat Littlewood polynomials exist`, Annals of Math, 192 (3) 2020.
-/

set_option autoImplicit false

namespace FlatLittlewoodPoly

open scoped Polynomial

/-- **Littlewood polynomials.** A polynomial $P$ over a ring $F$, of degree $n$ (with the zero
polynomial taken to have degree $0$), is a Littlewood polynomial if each of its coefficients of
$X^0, X^1, \ldots, X^n$ is $1$ or $-1$. -/
def IsLittlewoodPolynomial {F : Type*} [Ring F] (P : F[X]) : Prop :=
  ∀ i ≤ P.natDegree, P.coeff i = 1 ∨ P.coeff i = -1

/--
**Flat Littlewood polynomials exist.** There exist real constants $\Delta > \delta > 0$ such
that for every natural number $n \ge 2$ there is a Littlewood polynomial $P$ with complex
coefficients and of degree $n$ such that $\delta \sqrt{n} \le |P(z)| \le \Delta \sqrt{n}$ for all
$z \in \mathbb{C}$ with $|z| = 1$.

Source: P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, and M. Tiba, `Flat Littlewood polynomials exist`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-FlatLittlewoodPoly.lean Via leanprover/lean-eval@38361be, problem `annals_flat_littlewood_poly`.
-/
public theorem_wanted theorem_1_1 :
    ∃ Δ δ : ℝ, Δ > δ ∧ δ > 0 ∧ ∀ n ≥ 2,
      ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = n ∧
      ∀ z : ℂ, ‖z‖ = 1 → δ * √n ≤ ‖P.eval z‖ ∧
      ‖P.eval z‖ ≤ Δ * √n

end FlatLittlewoodPoly

end MathlibExt.Analysis.FlatLittlewoodPolyWanted
