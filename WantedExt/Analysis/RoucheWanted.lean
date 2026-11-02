/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rouche theorem via zero counting

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ComplexAnalysis.Rouche` — rouche_zero_count_eq (manifest `manifests/problems/rouche_zero_count_eq.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RoucheWanted` namespace. Mathematical
statements are unchanged. Source: Classical theorem in complex analysis.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

@[expose] public section

namespace MathlibExt.Analysis.RoucheWanted
namespace ComplexAnalysis

open MeromorphicOn

/-!
Rouché's theorem (zero-count formulation, extended to the meromorphic case via divisors),
stated as equality of multiplicity-counted zero counts on the closed disk of radius `R`
centered at `0`.

The previous formulation used `ValueDistribution.logCounting f 0 R`, the **log-weighted**
Nevanlinna counting function — which is *not* the conclusion of Rouché. Under `‖g‖ < ‖f‖`
on the boundary, `f` and `f + g` have the same number of zeros (counted with multiplicity)
inside the disk, but the log-weighted count depends on where each zero sits. Concretely,
`f(z) = z` and `g(z) = -1/2` satisfy `|g| = 1/2 < 2 = |z| = |f|` on `|z| = 2`, yet
`logCounting f 0 2 = log 2` while `logCounting (f + g) 0 2 = log(2 / (1/2)) = log 4`.

We instead state the conclusion as the equality of the multiplicity sums of the zero
divisors of `f` and `f + g` taken on the closed disk of radius `R`.

We also require `f` to be in *normal form* (`MeromorphicNFOn`) rather than merely
`MeromorphicOn`. A bare `MeromorphicOn` hypothesis admits functions whose pointwise values
disagree with their meromorphic order at exceptional points (any `=ᶠ[codiscreteWithin]`
modification is still meromorphic), and that pointwise disagreement is enough to make the
divisor identity fail. See the Zulip discussion at
https://leanprover.zulipchat.com/#narrow/channel/583341-Model-comparisons-for-Lean/topic/LeanEval/near/593331158
for a concrete counterexample to the previous `MeromorphicOn`-only formulation.
-/
/-- **Rouché's theorem.** Let $R > 0$, let $f : \mathbb{C} \to \mathbb{C}$ be meromorphic on
$\mathbb{C}$ and in normal form (at every point $f$ is either analytic, or has a pole and takes
the value $0$ there), and let $g : \mathbb{C} \to \mathbb{C}$ be analytic on $\mathbb{C}$.
If $|g(z)| < |f(z)|$ for every $z$ with $|z| = R$, then $f + g$ and $f$ have the same number
of zeros in the closed disk $|z| \le R$, counted with multiplicity: the sum over the points of
the disk of the positive part of the order of $f + g$ equals the same sum for $f$.

Source: E. Rouché, *Mémoire sur la série de Lagrange*, J. École Polytechnique 22 (1862) (Rouché's theorem). Via leanprover/lean-eval@38361be, problem `rouche`. -/
public theorem_wanted rouche_zero_count_eq
    {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : MeromorphicNFOn f Set.univ)
    (hg : AnalyticOn ℂ g Set.univ)
    (hbound : ∀ z : ℂ, ‖z‖ = R → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z, ((divisor (f + g) (Metric.closedBall 0 R))⁺) z) =
      (∑ᶠ z, ((divisor f (Metric.closedBall 0 R))⁺) z)

end ComplexAnalysis

end MathlibExt.Analysis.RoucheWanted
