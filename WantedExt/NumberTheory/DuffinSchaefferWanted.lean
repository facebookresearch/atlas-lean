/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Duffin-Schaeffer conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.DuffinSchaeffer` — duffin_schaeffer (manifest `manifests/problems/duffin_schaeffer.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.DuffinSchaefferWanted` namespace. Mathematical
statements are unchanged. Source: D. Koukoulopoulos and J. Maynard, 'On the Duffin-Schaeffer conjecture', Ann. of Math. 192 (2020), 251-307, https://doi.org/10.4007/annals.2020.192.1.5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.WellApproximable

@[expose] public section

namespace MathlibExt.NumberTheory.DuffinSchaefferWanted
namespace NumberTheory.DuffinSchaeffer

/-!
# The Duffin-Schaeffer conjecture

Koukoulopoulos and Maynard proved the Duffin-Schaeffer conjecture, giving
the exact divergence criterion for almost every real number to admit
infinitely many prescribed approximations by reduced fractions.

Mathlib already defines `addWellApproximable UnitAddCircle delta` as the
set of points lying within `delta n` of a point of exact additive order `n`
for infinitely many positive `n`. Points of exact order `n` on the unit
circle are precisely reduced fractions with denominator `n`.
-/

open MeasureTheory

/- **Koukoulopoulos-Maynard theorem (Duffin-Schaeffer conjecture).** For nonnegative
approximation radii `delta`, the corresponding limsup set of reduced
rational approximations has full measure exactly when
`sum_n phi(n) * delta(n)` diverges. -/
/-- Source: D. Koukoulopoulos and J. Maynard, 'On the Duffin-Schaeffer conjecture', Ann. of Math. 192 (2020), 251-307, https://doi.org/10.4007/annals.2020.192.1.5. Via leanprover/lean-eval@38361be, problem `duffin_schaeffer`. -/
public theorem_wanted duffin_schaeffer (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) :
    volume (addWellApproximable UnitAddCircle δ) = 1 ↔
      ¬ Summable fun n : ℕ => n.totient * δ n

end NumberTheory.DuffinSchaeffer

end MathlibExt.NumberTheory.DuffinSchaefferWanted
