/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equiangular lines with a fixed angle

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.EquiangularLinesFixedAngle` — annals_equiangular_lines_fixed_angle (manifest `manifests/problems/annals_equiangular_lines_fixed_angle.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted` namespace. Mathematical
statements are unchanged. Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-EquiangularLinesFixedAngle.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

@[expose] public section

namespace MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted
/-!
# Main Statement from Equiangular lines with a fixed angle

We formalise the statement of the main result from Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and
Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

namespace EquiangularLinesFixedAngle

open Filter

open scoped RealInnerProductSpace

/-- **Equiangular systems of unit vectors.** For a real number $\alpha$ and a natural number $d$,
an equiangular system with inner product $\pm\alpha$ in $\mathbb{R}^d$ is a set of unit vectors in
$d$-dimensional Euclidean space such that any two distinct vectors $x$ and $y$ in it satisfy
$|\langle x, y \rangle| = \alpha$.

Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`,
Annals of Math, 194 (3) 2021, third paragraph of the introduction. -/
structure EquiangularLines (α : ℝ) (d : ℕ) where
  /-- The set of unit vectors in `d`-dimensional Euclidean space. -/
  carrier : Set (EuclideanSpace ℝ (Fin d))
  norm : ∀ x ∈ carrier, ‖x‖ = 1
  angle : carrier.Pairwise fun x y ↦ |⟪x, y⟫| = α

/-- **Maximum number of equiangular lines.** For a real number $\alpha$ and a natural number $d$,
$N_\alpha(d)$ is the supremum, taken in $\mathbb{N}$, of the cardinalities of the equiangular
systems of unit vectors in $\mathbb{R}^d$ with inner product $\pm\alpha$. Here an infinite set
counts as having cardinality $0$, and a set of natural numbers that is not bounded above has
supremum $0$.

For $0 \le \alpha < 1$ these cardinalities are at most $\binom{d+1}{2}$ by Gerzon's bound, and a
system contains at most one of $x$ and $-x$, so $N_\alpha(d)$ is the maximum number of lines
through the origin in $\mathbb{R}^d$ with pairwise angle $\arccos \alpha$.

Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`,
Annals of Math, 194 (3) 2021, third paragraph of the introduction. -/
noncomputable def N (α : ℝ) (d : ℕ) : ℕ := ⨆ E : EquiangularLines α d, E.carrier.ncard

open Classical in
/-- **Spectral radius order.** For a real number $\lambda$, the spectral radius order
$k(\lambda) \in \mathbb{N} \cup \{\infty\}$ is the least natural number $k$ such that some simple
graph on $k$ vertices has an adjacency matrix with spectral radius $\max(\lambda, 0)$, and
$k(\lambda) = \infty$ if there is no such graph.

The source defines $k(\lambda)$ only for $\lambda > 0$, where $\max(\lambda, 0) = \lambda$.

Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`,
Annals of Math, 194 (3) 2021, Definition 1.1. -/
noncomputable def spectralRadiusOrder (lambda : ℝ) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | ∃ G : SimpleGraph (Fin k), spectralRadius ℝ (G.adjMatrix ℝ) = .ofReal lambda}, k

/-
Note that if `λ > 0` then `spectralRadiusOrder λ` cannot be `0` or `1`, because the spectral
radius of the adjacency matrix of any graph with no edges is `0`. So our subtractions
and divisions below are not pathological.
-/

/--
**Equiangular lines with a fixed angle.** Fix a real number $\alpha$ with $0 < \alpha < 1$, let
$\lambda = (1 - \alpha)/(2\alpha)$ and let $k = k(\lambda)$ be the spectral radius order of
$\lambda$. Let $N_\alpha(d)$ be the maximum number of equiangular lines in $\mathbb{R}^d$ with
common angle $\arccos \alpha$. Then:
(a) if $k < \infty$, then $N_\alpha(d) = \lfloor k(d - 1)/(k - 1) \rfloor$ for all sufficiently
large $d$;
(b) if $k = \infty$, then $N_\alpha(d) = d + o(d)$ as $d \to \infty$.

Source: Z. Jiang, J. Tidor, Y. Yao, S. Zhang, and Y. Zhao, `Equiangular lines with a fixed angle`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-EquiangularLinesFixedAngle.lean Via leanprover/lean-eval@38361be, problem `annals_equiangular_lines_fixed_angle`.
-/
public theorem_wanted theorem_1_2 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    let k := spectralRadiusOrder ((1 - α) / (2 * α))
    (k < ⊤ → ∀ᶠ d in atTop, N α d = ⌊(k.toNat * (d - 1) : ℝ) / (k.toNat - 1 : ℝ)⌋₊) ∧
    (k = ⊤ → ∃ e : ℕ → ℝ, e =o[atTop] (Nat.cast : ℕ → ℝ) ∧ ∀ d, N α d = d + e d)

end EquiangularLinesFixedAngle

end MathlibExt.Combinatorics.EquiangularLinesFixedAngleWanted
