/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CompactlyGenerated.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits

namespace MathlibExtTest.Topology.Category.CompactlyGenerated.ColimitsTests

#synth HasColimitsOfSize.{0, 0} CompactlyGenerated.{0, 0}
#synth HasColimitsOfSize.{1, 1} CompactlyGenerated.{1, 1}
#synth HasColimitsOfSize.{1, 1} CompactlyGenerated.{0, 1}

example : HasColimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
  inferInstance

section ParallelPair

variable (F : WalkingParallelPair ⥤ CompactlyGenerated.{u, v})

example : F.obj WalkingParallelPair.zero ⟶ colimit F :=
  colimit.ι F WalkingParallelPair.zero

example : F.obj WalkingParallelPair.one ⟶ colimit F :=
  colimit.ι F WalkingParallelPair.one

end ParallelPair

#print axioms CompactlyGenerated.instHasColimitsOfSize

attribute [-instance] CompactlyGenerated.instHasColimitsOfSize in
example : True := by
  fail_if_success
    let _ : HasColimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
      inferInstance
  trivial

end MathlibExtTest.Topology.Category.CompactlyGenerated.ColimitsTests
