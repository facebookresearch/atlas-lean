/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceGadgetCommaPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalReedyGadgetCommaPoint
import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenAIndependentHoms

/-!
# Genuine original full gadget Quillen A maps

Both original full input functors have their actual complete original
comma nerve point maps weak. The canonical genuine Quillen A theorem
supplies the same full original nerve maps from the explicit native
source-object lifts. Every original map and coefficient universe remains.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.CoherentRealization.OriginalGadgetComparison

open OriginalPointed OriginalNecklaceInput OriginalFixedFrontContraction

/-- The same full original native-to-gadget nerve map from the explicit original input object-universe lift is weak. -/
theorem nativeGadgetInputs_liftedNerve_weak (K : OriginalPointed.Category.{u}) :
    SSet.realizationWeakEquivalences (nerveMap
      (ULift.downFunctor.{u,u,u+1} ⋙ ULiftHom.down.{0,u,u} ⋙ nativeGadgetInputs K)) :=
  SSet.nerveMap_liftedSourceHom_weak_of_rightComma (nativeGadgetInputs K) (nativeGadgetCommaNerve_point_weak K)

/-- The same full original Reedy-to-fibrant-gadget nerve map from its explicit original input object-universe lift is
weak. -/
theorem reedyFibrantInputs_liftedNerve_weak (K : OriginalPointed.Category.{u}) :
    SSet.realizationWeakEquivalences (nerveMap
      (ULift.downFunctor.{u,u,u+1} ⋙ ULiftHom.down.{0,u,u} ⋙ reedyIntoFibrantGadgetInputs K)) :=
  SSet.nerveMap_liftedSourceHom_weak_of_rightComma (reedyIntoFibrantGadgetInputs K)
    (reedyGadgetCommaNerve_point_weak K)

end CategoryTheory.CoherentRealization.OriginalGadgetComparison
