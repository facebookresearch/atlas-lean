/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of `exists_seven_coloring` is adapted from OpenAI Math,
`lean/ComparatorChallenges/PlaneColoring.lean`, at commit
`3344da59991ed94f9ba711217b29c1d760badfa6`:
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlaneColoring.lean#L9-L15
The source is distributed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Its file and license notices do
not specify a copyright holder or author for this statement.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace WantedExt.Geometry.PlaneUnitDistance

/-- There is a coloring of the entire Euclidean plane with seven colors in which any
pair of points at distance exactly one has different colors. No measurability or other
regularity is imposed, and the condition holds at every point, including boundaries.

Source: [OpenAI Math, `properColoring_seven`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlaneColoring.lean#L10-L15).

Source: Classical upper bound by Isbell's hexagonal tiling (1950), as credited in
[Aubrey D. N. J. de Grey, *The chromatic number of the plane is at least 5*, §1 (2018)](https://arxiv.org/pdf/1804.02385). -/
public theorem_wanted exists_seven_coloring :
    ∃ c : EuclideanSpace ℝ (Fin 2) → Fin 7,
      ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y

end WantedExt.Geometry.PlaneUnitDistance
