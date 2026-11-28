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

public import MathlibExt.Geometry.PlaneUnitDistanceSevenColor
import Batteries.Util.ProofWanted
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
