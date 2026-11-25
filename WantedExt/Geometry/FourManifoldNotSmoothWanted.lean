/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Freedman's non-smoothability theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.FourManifoldNotSmooth` — four_manifold_not_smooth (manifest `manifests/problems/four_manifold_not_smooth.toml`, rev 1, submitter Oliver Nash, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.FourManifoldNotSmoothWanted` namespace. Mathematical
statements are unchanged. Source:
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.FourManifoldNotSmoothWanted
/-!

# Non-smoothable compact four-manifolds

In 1982, Freedman proved that every symmetric unimodular bilinear form over `ℤ` arises as the
intersection form of a closed, oriented, simply-connected topological 4-manifold. In particular
there exists such a manifold with the `E₈` form as intersection form (moreover because `E₈` is
even, this is the unique such manifold with this intersection form). However by Rokhlin's theorem
(or Donaldson's theorem) there is no (closed, oriented, simply-connected) smooth four-manifold with
this intersection form.

We ask here for a proof of the corollary: there exists a closed, simply-connected, topological
four-manifold which cannot be smoothed.

# References:
- Freedman, M., The topology of four-dimensional manifolds, JDG. pp 357--453, 17(3) (1982)

-/

namespace Geometry

open scoped Manifold ContDiff

local notation "𝔼" => EuclideanSpace ℝ (Fin 4)

/- Freedman's theorem: there exists a closed, simply-connected, topological four-manifold which
cannot be smoothed.

Note the fact that `M` is boundaryless follows from `ModelWithCorners.instBoundarylessManifold`. -/
/-- **A closed simply connected topological 4-manifold with no smooth structure.** There
exists a compact, Hausdorff, simply connected topological space $M$ that admits an atlas of
charts modelled on $\mathbb{R}^4$, such that no atlas of charts on $M$ modelled on $\mathbb{R}^4$
makes $M$ a smooth ($C^\infty$) manifold.

Source: see manifest Via leanprover/lean-eval@38361be, problem `four_manifold_not_smooth`. -/
public theorem_wanted four_manifold_not_smooth :
    ∃ (M : Type*) (_ : TopologicalSpace M) (_ : T2Space M) (_: CompactSpace M)
      (_ : SimplyConnectedSpace M) (_ : Nonempty (ChartedSpace 𝔼 M)),
      ∀ (_ : ChartedSpace 𝔼 M), ¬ IsManifold (𝓡 4) ∞ M

end Geometry

end MathlibExt.Geometry.FourManifoldNotSmoothWanted
