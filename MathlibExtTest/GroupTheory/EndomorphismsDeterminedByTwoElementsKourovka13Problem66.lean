/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66

namespace MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted

/-- The refutation rules out two elements determining the endomorphisms with non-cyclic
images at every finite rank. -/
example (hall : ∀ n : ℕ, DeterminedByTwoElements (FreeMetabelianGroup n)) : False :=
  freeMetabelianEndomorphismsDeterminedByTwoElements_refuted hall

/-- The refutation says that some finite rank fails to have two determining elements. -/
example : ∃ n : ℕ, ¬ DeterminedByTwoElements (FreeMetabelianGroup n) :=
  not_forall.mp freeMetabelianEndomorphismsDeterminedByTwoElements_refuted

end MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted
