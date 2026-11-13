/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Runge's theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.Runge` — runge_theorem (manifest `manifests/problems/runge_theorem.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RungeWanted` namespace. Mathematical
statements are unchanged. Source: C. Runge, *Zur Theorie der eindeutigen analytischen Funktionen*, Acta Math. 6 (1885), 229-244. Listed as §64 (additional statement 3) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.RungeWanted
namespace ComplexAnalysis

/-!
# Runge's theorem

Basic Runge approximation theorem for compact subsets of `ℂ`: if `K` is
compact and `f` is analytic on an open neighbourhood of `K`, then `f`
can be uniformly approximated on `K` by rational functions with no
poles on `K`.

This is the basic form. It does not include the standard pole-control
refinement, where poles may be chosen from prescribed points, one in
each connected component of `ℂ \ K`.
-/

open scoped Polynomial

/- **Runge's theorem.** If `K ⊆ ℂ` is compact and `f` is analytic on
an open neighbourhood of `K`, then for every `ε > 0`, `f` is uniformly
approximated on `K` by a rational function `p / q` with `q` non-vanishing
on `K`. -/
/-- **Runge's theorem.** Let $K \subseteq \mathbb{C}$ be compact, let $U \subseteq \mathbb{C}$ be
open with $K \subseteq U$, and let $f : \mathbb{C} \to \mathbb{C}$ be analytic at every point of
$U$. Then for every real $\varepsilon > 0$ there are complex polynomials $p$ and $q$ such that
$q(z) \ne 0$ for every $z \in K$ and $|f(z) - p(z)/q(z)| < \varepsilon$ for every $z \in K$.

Source: C. Runge, *Zur Theorie der eindeutigen analytischen Funktionen*, Acta Math. 6 (1885), 229-244. Listed as §64 (additional statement 3) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `runge_theorem`. -/
public theorem_wanted runge (K : Set ℂ) (_hK : IsCompact K) (U : Set ℂ) (_hU : IsOpen U)
    (_hKU : K ⊆ U) (f : ℂ → ℂ) (_hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε)

end ComplexAnalysis

end MathlibExt.Analysis.RungeWanted
