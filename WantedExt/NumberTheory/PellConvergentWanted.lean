/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pell solutions are convergents of √d

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.PellConvergent` — pell_solution_convergent (manifest `manifests/problems/pell_solution_convergent.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.PellConvergentWanted` namespace. Mathematical
statements are unchanged. Source: J.-L. Lagrange (1770). Listed as §84 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.PellConvergentWanted
namespace NumberTheory

/-!
# Pell solutions are convergents of `√d`

§84 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. Lagrange's
theorem: if `d` is a positive squarefree integer and `(x, y)` is a positive
solution of Pell's equation `x² − d y² = 1`, then `x / y` occurs as a
convergent `pₙ / qₙ` of the regular continued fraction of `√d`, connecting the
arithmetic of Pell solutions with the continued-fraction expansion of a
quadratic irrational.

mathlib has the Pell solution group (`Pell.Solution₁`, `Pell.IsFundamental`)
and the continued-fraction algorithm `GenContFract.of` with its convergent
stream `GenContFract.convs`, but no link between the two: there is no
quadratic-irrational / eventually-periodic continued-fraction theory of `√d`,
and nothing relating Pell solutions to convergents.

Since `x² − d y² = 1` forces `gcd x y = 1`, and `convs n` is `pₙ / qₙ` in
lowest terms, `convs n = x / y` is the faithful reading of "`(x, y)` is of the
form `(pₙ, qₙ)`". For `d = 1` the hypotheses `0 < x`, `0 < y`, `x² − y² = 1`
are unsatisfiable; the content lives at squarefree `d ≥ 2`, where `√d` is
irrational and the continued fraction is infinite.
-/

open scoped Real

/- **Pell solutions are convergents of `√d`** (§84). Let `d` be a positive
squarefree integer and let `(x, y)` be a positive solution of Pell's equation
`x² − d y² = 1`. Then the ratio `x / y` is one of the convergents of the
regular continued fraction of `√d`: there is an index `n` with
`(GenContFract.of √d).convs n = x / y`. -/
/-- Source: J.-L. Lagrange (1770). Listed as §84 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `pell_solution_convergent`. -/
public theorem_wanted pell_solution_is_convergent
    (d : ℤ) (_hd : Squarefree d) (_hd0 : 0 < d)
    (x y : ℤ) (_hx : 0 < x) (_hy : 0 < y)
    (_hsol : x ^ 2 - d * y ^ 2 = 1) :
    ∃ n : ℕ, (GenContFract.of (Real.sqrt (d : ℝ))).convs n = (x : ℝ) / (y : ℝ)

end NumberTheory

end MathlibExt.NumberTheory.PellConvergentWanted
