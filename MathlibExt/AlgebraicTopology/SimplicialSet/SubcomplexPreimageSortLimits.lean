/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Original subcomplex preimages at all index sorts

The native preimage formulas are retained for arbitrary index sorts,
including the proposition indices in full finite unions and intersections.
The existing type-indexed formulas do not cover these inner bounds.
-/

universe u v
open CategoryTheory

namespace SSet.Subcomplex

variable {X Y : SSet.{u}}

/-- The native original preimage preserves full unions indexed by any sort. -/
theorem preimage_iSup_of_sort {I : Sort v} (A : I → X.Subcomplex) (p : Y ⟶ X) :
    (⨆ i, A i).preimage p = ⨆ i, (A i).preimage p := by
  ext q x
  simp only [Subfunctor.iSup_obj, preimage_obj, Set.mem_preimage, Set.mem_iUnion]

/-- The native original preimage preserves full intersections indexed by any sort. -/
theorem preimage_iInf_of_sort {I : Sort v} (A : I → X.Subcomplex) (p : Y ⟶ X) :
    (⨅ i, A i).preimage p = ⨅ i, (A i).preimage p := by
  ext q x
  simp only [Subfunctor.iInf_obj, preimage_obj, Set.mem_preimage, Set.mem_iInter]

end SSet.Subcomplex
