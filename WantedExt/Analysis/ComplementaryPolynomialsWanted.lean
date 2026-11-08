/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complementary polynomial on the unit circle

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.ComplementaryPolynomials` — exists_complementary_polynomial_on_unit_circle (manifest `manifests/problems/exists_complementary_polynomial_on_unit_circle.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.ComplementaryPolynomialsWanted` namespace. Mathematical
statements are unchanged. Source: https://link.springer.com/article/10.1007/s00220-025-05302-9
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.Complex.Circle

@[expose] public section

namespace MathlibExt.Analysis.ComplementaryPolynomialsWanted
namespace ComplexAnalysis

open Polynomial

/-!
Complementary polynomials on the unit circle.

This is the basic existence statement appearing in quantum signal processing: if a complex
polynomial has sup norm at most `1` on the unit circle, then it admits a complementary polynomial
whose squared moduli add up to `1` on the circle.

The previous statement asked for `Q.natDegree = P.natDegree` (strict equality), which fails on
the boundary case `P = X`: there `|P(z)| = 1` on the entire unit circle, so any complementary `Q`
must vanish on the circle and hence be the zero polynomial; but `natDegree 0 = 0 ≠ 1 = natDegree X`.
We relax the constraint to `≤`, which is what Fejér-Riesz / spectral factorization actually
delivers (the degree of `Q` is at most that of `P`, with equality generically).
-/

/- If `P` is bounded by `1` on the unit circle, then there is a polynomial `Q` of degree at most
that of `P` whose squared moduli complement `P` to `1` on the unit circle. -/
/-- Source: https://link.springer.com/article/10.1007/s00220-025-05302-9 Via leanprover/lean-eval@38361be, problem `exists_complementary_polynomial_on_unit_circle`. -/
public theorem_wanted exists_complementary_polynomial_on_unit_circle
    (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1

end ComplexAnalysis

end MathlibExt.Analysis.ComplementaryPolynomialsWanted
