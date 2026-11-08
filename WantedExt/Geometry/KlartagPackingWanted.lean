/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Klartag's construction of lattice sphere packings

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.KlartagPacking` — klartag_packing (manifest `manifests/problems/klartag_packing.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.KlartagPackingWanted` namespace. Mathematical
statements are unchanged except that the packing theorem is quantified directly over positive dimensions `Fin n` with `0 < n` instead of the source's shifted `Fin (n + 1)` indexing. Source:
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.KlartagPackingWanted
/-!
# Klartag's construction of lattice sphere packings

Boaz Klartag proved in 2025 that in any dimension n there exists an ellipsoid E ⊂ ℝⁿ of
volume cn² centered at the origin that contains no points of ℤⁿ \ {0}, where c > 0 is
a universal constant. Equivalently, there exists a lattice sphere packing in ℝⁿ whose
density is at least cn²2⁻ⁿ, improving over previously known constructions of (not
necessarily lattice) sphere packings that yielded densities of at most cn⋅log(n)⋅2⁻ⁿ.
The proof utilizes a stochastically evolving ellipsoid that accumulates at least cn²
lattice points on its boundary.

## References

* Boaz Klartag. Lattice packing of spheres in high dimensions using a stochastically evolving ellipsoid. https://arxiv.org/abs/2504.05042

* https://gilkalai.wordpress.com/2025/04/09/boaz-klartag-striking-new-lower-bounds-for-sphere-packing-in-high-dimensions/

* https://www.quantamagazine.org/new-sphere-packing-record-stems-from-an-unexpected-source-20250707/
-/

namespace Geometry.KlartagPacking

/- Klartag's theorem. In the statement, the ellipsoid E is realized as the image of a ball
under a linear map, which we do not require to be of full rank, since if it is not of full
rank, then the volume of E is zero and the conclusion is not satisfied. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `klartag_packing`. -/
public theorem_wanted klartag_packing : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
    let V := EuclideanSpace ℝ (Fin n)
    ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
      (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
      {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0}

end Geometry.KlartagPacking

end MathlibExt.Geometry.KlartagPackingWanted
