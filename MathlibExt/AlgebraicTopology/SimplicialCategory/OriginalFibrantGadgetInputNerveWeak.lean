/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedFibrantInputReplacementUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

/-!
# Genuine original fibrant-gadget input inclusion nerve weakness

Both full original replacement units retain every original pointed
input and the same target retraction triangle. Their actual nerve
homotopies give an inverse of the same full original input inclusion
map, proving weakness without a comparison or localization certificate.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same full original fibrant input inclusion is weak on its actual whole original nerve, from a genuine original
target unit retraction. -/
theorem fibrantInputInclusion_nerve_weak (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K)
    (hr : replacementUnit.app K ≫ r = 𝟙 K) :
    SSet.realizationWeakEquivalences (nerveMap (fibrantInputInclusion K)) := by
  let F := fibrantInputInclusion K
  let G := gadgetInputReplacement K r
  have hFG : SSet.Homotopy (𝟙 _) (nerveMap F ≫ nerveMap G) := by
    have h := NatTrans.nerveHomotopy (fibrantGadgetInputReplacementUnit K r hr)
    simpa only [nerveMap_id, nerveMap_comp] using h
  have hGF : SSet.Homotopy (𝟙 _) (nerveMap G ≫ nerveMap F) := by
    have h := NatTrans.nerveHomotopy (gadgetInputReplacementUnit K r hr)
    simpa only [nerveMap_id, nerveMap_comp] using h
  let h : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (CostructuredArrow fibrantGadgetFullInclusion K)))
      (SSet.toTop.obj (nerve (CostructuredArrow gadgetInclusion K))) :=
    { toFun := (SSet.toTop.map (nerveMap F)).hom
      invFun := (SSet.toTop.map (nerveMap G)).hom
      left_inv := by
        have h := (SSet.realizeHomotopy _ _ _ _ hFG).symm
        refine ⟨?_⟩
        simpa only [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using h
      right_inv := by
        have h := (SSet.realizeHomotopy _ _ _ _ hGF).symm
        refine ⟨?_⟩
        simpa only [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using h }
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map (nerveMap F))
  exact TopCat.mem_of_eq_toFun h rfl

end CategoryTheory.CoherentRealization.OriginalPointed
