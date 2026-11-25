/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion

/-!
# Coherent zero-extension and its actual circle descent

These constructors implement the interval-coordinate source in BGT
Section 7.1, pages 44--45. The output contracts fix the whole diagram at
both diagonal intervals and at (0,1), all old ordinal maps, and the
value of the based structure map on every simplex of Delta[1].
No K-theory vanishing, additivity or universal-invariant theorem is input.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion

open StableInfinityCategoryModels

universe u

/-- Extend every full multi-gap diagram along the new interval factor. -/
def_wanted coherent_interval_insertion (C : StableInfinityCategory.{u}) :
  IntervalInsertion C

/-- Use the actual zero diagram to point every native diagonal space. -/
def_wanted native_multi_s_pointing (C : StableInfinityCategory.{u}) :
  MultiSPointing C

/-- Descend the interval insertion along the native circle and smash quotients. -/
def_wanted native_circle_insertion (C : StableInfinityCategory.{0}) :
  CircleInsertion C

end MathlibExt.AlgebraicTopology.StableInfinityIntervalInsertion
