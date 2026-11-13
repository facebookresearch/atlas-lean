/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Schmidt's subspace theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.SchmidtSubspace` — schmidt_subspace (manifest `manifests/problems/schmidt_subspace.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.SchmidtSubspaceWanted` namespace. Mathematical
statements are unchanged. Source: W.M. Schmidt, Diophantine approximation, Lecture Notes in Mathematics 785, Springer Verlag 1980, Chap. V,VI,VII.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.SchmidtSubspaceWanted
/-!
# Schmidt's subspace theorem

https://en.wikipedia.org/wiki/Subspace_theorem

If L₁, …, Lₙ are ℂ-linearly independent linear forms in `n` variables with
algebraic coefficients and if ε>0 is any given real number, then the non-zero
integer points `x` with |L₁(x) … Lₙ(x)| < |x|^−ε lie in a finite number of proper
subspaces of ℚⁿ. The specialization n = 2 gives the Thue–Siegel–Roth theorem
(also in LeanEval as `thueSiegelRoth` and already solved on Jun 22, 2026).

## References

W.M. Schmidt, Diophantine approximation, Lecture Notes in Mathematics 785, Springer Verlag 1980, Chap. V,VI,VII.

The slides https://pub.math.leidenuniv.nl/~evertsejh/14-bonn.pdf present
Faltings’ product theorem, which gives a new proof and strong quantitative
versions of Schmidt’s subspace theorem.

https://pub.math.leidenuniv.nl/~evertsejh/dio19-7.pdf (course notes)
-/

namespace NumberTheory.SchmidtSubspace

/- **Schmidt's subspace theorem**.

In our statement, we use an arbitrary Fintype σ with at least two elements instead of
`Fin n`, and use the fact that every proper subspace is contained in a codimension 1
subspace, which is described by the vanishing of a linear form with coefficients in ℤ. -/
/-- **Schmidt's subspace theorem.** Let $\sigma$ be a finite set with at least two elements, and
for $i \in \sigma$ let $L_i(x) = \sum_{j \in \sigma} a_{ij} x_j$ be linear forms whose
coefficients $a_{ij} \in \mathbb{C}$ are algebraic over $\mathbb{Q}$ and whose coefficient
vectors $(a_{ij})_{j \in \sigma}$ are linearly independent over $\mathbb{C}$. Let
$\varepsilon > 0$ be real. Then there is a finite set $S$ of nonzero vectors in
$\mathbb{Z}^\sigma$ such that every $x \in \mathbb{Z}^\sigma$ with
$\left|\prod_{i \in \sigma} L_i(x)\right| < \|x\|^{-\varepsilon}$, where
$\|x\| = \max_{j \in \sigma} |x_j|$, satisfies $\sum_{i \in \sigma} c_i x_i = 0$ for some $c \in S$.

Every proper subspace of $\mathbb{Q}^\sigma$ lies in a hyperplane $\sum_i c_i x_i = 0$ with a
nonzero integer vector $c$, so this is the usual form: these $x$ lie in finitely many proper
subspaces.

Source: W.M. Schmidt, Diophantine approximation, Lecture Notes in Mathematics 785, Springer Verlag 1980, Chap. V,VI,VII. Via leanprover/lean-eval@38361be, problem `schmidt_subspace`. -/
public theorem_wanted schmidt_subspace (σ : Type*) [Fintype σ] (hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ)
    (alg : ∀ i j, IsAlgebraic ℚ (L i j)) (ind : LinearIndependent ℂ L)
    (ε : ℝ) (pos : 0 < ε) :
    ∃ s : Finset (σ → ℤ), 0 ∉ s ∧ ∀ x : σ → ℤ,
      ‖∏ i, ∑ j, L i j * x j‖ < ‖x‖ ^ (-ε) → ∃ c ∈ s, ∑ i, c i * x i = 0

end NumberTheory.SchmidtSubspace

end MathlibExt.NumberTheory.SchmidtSubspaceWanted
