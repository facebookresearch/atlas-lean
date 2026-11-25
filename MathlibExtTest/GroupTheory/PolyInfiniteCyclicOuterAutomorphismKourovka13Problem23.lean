/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23

namespace MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted

example (claim : polyInfiniteCyclicHasOuterAutomorphism) : False :=
  polyInfiniteCyclicHasOuterAutomorphism_refuted claim

example : HasNormalSeriesInfiniteCyclicFactors PUnit := by
  refine ⟨0, fun _ => ⊥, rfl, ?_, fun _ => inferInstance, Fin.elim0⟩
  ext g
  have h : g = 1 := Subsingleton.elim _ _
  simp [h]

end MathlibExt.GroupTheory.PolyInfiniteCyclicOuterAutomorphismKourovka13Problem23Wanted
