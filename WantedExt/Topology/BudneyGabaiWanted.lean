/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Budney--Gabai knotted three-spheres in S¹ × S³

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.BudneyGabai` — budney_gabai_knotted_three_spheres (manifest `manifests/problems/budney_gabai_knotted_three_spheres.toml`, rev 1, submitter Vasily Ilin, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.BudneyGabaiWanted` namespace. Mathematical
statements are unchanged. Source: R. Budney and D. Gabai, 'Knotted 3-balls in S⁴', Corollary 8.6, arXiv:1912.09029v3 (2021), https://arxiv.org/abs/1912.09029.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.BudneyGabaiWanted
namespace Topology

open scoped ContDiff Manifold
open Metric (sphere)

/-!
# Budney--Gabai knotted three-spheres

Corollary 8.6 of Budney and Gabai's *Knotted 3-balls in S^4* states that
`S^1 × S^3` contains infinitely many isotopy classes of embedded three-spheres
homotopic to the standard cross-section `{x₀} × S^3`.

Here `S^1` and `S^3` are the unit spheres in Euclidean two- and four-space.
An isotopy of unparameterized embedded spheres is expressed as a jointly smooth
one-parameter family of smooth embeddings, with equality of ranges at its
endpoints. By the smooth isotopy extension theorem, this agrees with ambient
smooth isotopy. The connected-complement condition records that every sphere is
nonseparating.
-/

/- **Budney--Gabai, Corollary 8.6.** There are infinitely many pairwise smoothly
non-isotopic, nonseparating embedded three-spheres in `S^1 × S^3`, all homotopic
to the standard cross-section `{x₀} × S^3`. -/
/-- Source: R. Budney and D. Gabai, 'Knotted 3-balls in S⁴', Corollary 8.6, arXiv:1912.09029v3 (2021), https://arxiv.org/abs/1912.09029. Via leanprover/lean-eval@38361be, problem `budney_gabai_knotted_three_spheres`. -/
public theorem_wanted budney_gabai_knotted_three_spheres
    (x₀ : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ∃ e : ℕ → sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
        sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
          sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      (∀ n,
        Manifold.IsSmoothEmbedding
            (𝓡 3) ((𝓡 1).prod (𝓡 3)) ∞ (e n) ∧
          IsConnected (Set.range (e n))ᶜ ∧
          ∃ K : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
              sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
                sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
            Continuous K ∧
              (∀ p, K (0, p) = e n p) ∧
              ∀ p, K (1, p) = (x₀, p)) ∧
        ∀ i j, i ≠ j →
          ¬ ∃ H : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
              sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
                sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
            ContMDiff
                ((𝓡∂ 1).prod (𝓡 3)) ((𝓡 1).prod (𝓡 3)) ∞ H ∧
              (∀ t,
                Manifold.IsSmoothEmbedding
                  (𝓡 3) ((𝓡 1).prod (𝓡 3)) ∞ (fun p ↦ H (t, p))) ∧
              Set.range (fun p ↦ H (0, p)) = Set.range (e i) ∧
              Set.range (fun p ↦ H (1, p)) = Set.range (e j)

end Topology

end MathlibExt.Topology.BudneyGabaiWanted
