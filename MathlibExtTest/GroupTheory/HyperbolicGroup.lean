/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.HyperbolicGroup
public import MathlibExt.GroupTheory.HyperbolicGroupExamples
public import Mathlib.Algebra.Group.TypeTags.Finite

@[expose] public section

namespace MathlibExtTest.HyperbolicGroup

/-- Regression test for the Gromov-product basepoint order: an infinite group is word-hyperbolic
(`Group.isHyperbolic_multiplicative_int`). With the basepoint misread as the third argument,
`Group.IsHyperbolic` holds only for finite groups. -/
example : ¬ ∀ (G : Type) [Group G], Group.IsHyperbolic G → Finite G := fun h =>
  (h _ Group.isHyperbolic_multiplicative_int).false

end MathlibExtTest.HyperbolicGroup
