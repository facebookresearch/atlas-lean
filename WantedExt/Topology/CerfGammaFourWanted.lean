/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cerf's theorem: every self-diffeomorphism of S3 is smoothly isotopic to a linear isometry

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.CerfGammaFour` — cerf_gamma_four (manifest `manifests/problems/cerf_gamma_four.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.CerfGammaFourWanted` namespace. Mathematical
statements are unchanged. Source: J. Cerf, Sur les diffeomorphismes de la sphere de dimension trois, Lecture Notes in Mathematics 53, Springer (1968).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace MathlibExt.Topology.CerfGammaFourWanted
namespace Topology

open scoped Manifold ContDiff
open Metric (sphere)

/-!
# Cerf's theorem Γ₄ = 0 (1968)

Cerf's theorem states that every self-diffeomorphism of the standard 3-sphere is
smoothly isotopic to the restriction of a linear isometry of ℝ⁴ — equivalently,
the inclusion `O(4) ↪ Diff(S³)` (acting by restriction of the linear action on ℝ⁴) is
surjective on π₀. The classical name `Γ₄ = 0` refers to Cerf's group of pseudo-isotopies
in dimension 4 (originally formulated as the obstruction to extending self-diffeomorphisms
of S³ across D⁴).

This is the unparameterized (X = point) case of the Smale conjecture (Hatcher 1983, see
`SmaleConjecture.lean`). It is historically and technically distinct from the full Smale
conjecture: Cerf's original proof predates Hatcher's by 15 years and uses pseudo-isotopy
theory rather than the bigon / 2-sphere configuration analysis Hatcher employs.

We state isotopy as a smooth map `[0, 1] × S³ → S³` whose every time slice is a
diffeomorphism, witnessed by an explicit smooth slice-inverse `F'`. Smoothness of `F`
and `F'` together with the pointwise-inverse identities forces each time-slice
`p ↦ F(t, p)` to be a diffeomorphism (its slice-inverse `p ↦ F'(t, p)` is smooth as a
composition with the smooth inclusion `p ↦ (t, p)`). This avoids the need for a topology
on `Diffeomorph S³ S³` (which mathlib does not yet have).
-/

/- **Cerf's theorem Γ₄ = 0.** Every self-diffeomorphism of S³ is smoothly isotopic to
the restriction of a linear isometry of ℝ⁴. -/
/-- **Cerf's theorem $\Gamma_4 = 0$.** Let $S^3 \subset \mathbb{R}^4$ be the unit sphere. Every
smooth diffeomorphism $f$ of $S^3$ is smoothly isotopic to the restriction of a linear isometry of
$\mathbb{R}^4$: there are an orthogonal matrix $A \in O(4)$ and smooth maps
$F, F' : [0, 1] \times S^3 \to S^3$ such that for every $t \in [0, 1]$ the maps $F(t, \cdot)$ and
$F'(t, \cdot)$ are inverse to each other, and $F(0, p) = f(p)$ and $F(1, p) = Ap$ for all
$p \in S^3$.

Source: J. Cerf, Sur les diffeomorphismes de la sphere de dimension trois, Lecture Notes in Mathematics 53, Springer (1968). Via leanprover/lean-eval@38361be, problem `cerf_gamma_four`. -/
public theorem_wanted cerf_gamma_four
    (f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯
         sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ∃ (A : Matrix.orthogonalGroup (Fin 4) ℝ)
      (F F' : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
              sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
      ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 3) ∞ F ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 3) ∞ F' ∧
      (∀ t p, F  (t, F' (t, p)) = p) ∧
      (∀ t p, F' (t, F  (t, p)) = p) ∧
      (∀ p, F (0, p) = f p) ∧
      (∀ p, (F (1, p) : EuclideanSpace ℝ (Fin 4)) =
            Matrix.UnitaryGroup.toLinearEquiv A
              (p : EuclideanSpace ℝ (Fin 4)))

end Topology

end MathlibExt.Topology.CerfGammaFourWanted
