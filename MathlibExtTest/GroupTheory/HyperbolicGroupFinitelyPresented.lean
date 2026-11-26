/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupHyperbolic
import MathlibExt.GroupTheory.HyperbolicGroupFinitelyPresented

namespace MathlibExtTest.GroupTheory.HyperbolicGroupFinitelyPresented

open MathlibExt.GroupTheory.HyperbolicGroupWanted

-- The empty generating family is allowed.
example {G : Type*} [Group G] [Subsingleton G] : Group.IsFinitelyPresented G :=
  isFinitelyPresented_of_isHyperbolic (Group.IsHyperbolic.of_subsingleton G)

-- Apply the theorem to an infinite nonabelian group with hyperbolicity constant zero.
example : Group.IsFinitelyPresented (FreeGroup (Fin 2)) :=
  isFinitelyPresented_of_isHyperbolic
    ⟨Fin 2, inferInstance, ⟨FreeGroup.of, FreeGroup.closure_range_of _⟩, 0,
      freeGroup_isDeltaHyperbolic_zero (Fin 2)⟩

end MathlibExtTest.GroupTheory.HyperbolicGroupFinitelyPresented
