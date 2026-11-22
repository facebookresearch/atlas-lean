/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFibrantGadgetInputNerveWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalGadgetQuillenAMaps

/-!
# The actual original target retraction for quasicategories

The original inner-horn unit lifts into the same original quasicategory.
Its complete pointed boundary and strict unit triangle are retained.
The two original gadget-input units consequently prove weakness of the
same fibrant-input inclusion and original Reedy input map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The actual original quasicategory target retracts its same full pointed replacement unit. -/
def quasiReplacementRetraction (K : Category.{u}) [SSet.Quasicategory K.right] :
    replacementFunctor.obj K ⟶ K :=
  Under.homMk (SSet.exists_innerHornReplacement_extension (𝟙 K.right)).choose (by
    change (K.hom ≫ SSet.innerHornReplacementUnit.app K.right) ≫
      (SSet.exists_innerHornReplacement_extension (𝟙 K.right)).choose = K.hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => K.hom ≫ f)
        (SSet.exists_innerHornReplacement_extension (𝟙 K.right)).choose_spec.1).trans
          (Category.comp_id _)))

/-- The same actual original target retraction retains the full pointed unit triangle. -/
theorem quasiReplacementRetraction_unit (K : Category.{u}) [SSet.Quasicategory K.right] :
    replacementUnit.app K ≫ quasiReplacementRetraction K = 𝟙 K := by
  apply Under.UnderMorphism.ext
  exact (SSet.exists_innerHornReplacement_extension (𝟙 K.right)).choose_spec.1

/-- The same complete original fibrant-gadget input inclusion nerve is weak over every actual original quasicategory
target. -/
theorem fibrantInputInclusion_nerve_weak_of_quasicategory
    (K : Category.{u}) [SSet.Quasicategory K.right] :
    SSet.realizationWeakEquivalences (nerveMap (fibrantInputInclusion K)) :=
  fibrantInputInclusion_nerve_weak K (quasiReplacementRetraction K)
    (quasiReplacementRetraction_unit K)

end CategoryTheory.CoherentRealization.OriginalPointed

namespace CategoryTheory.CoherentRealization.OriginalGadgetComparison

open OriginalPointed OriginalFixedFrontContraction

/-- The same original Reedy input map to all full gadgets is weak on its original nerve with explicit source object and
Hom universe lifts. -/
theorem reedyIntoGadgetInputs_liftedNerve_weak
    (K : OriginalPointed.Category.{u}) [SSet.Quasicategory K.right] :
    SSet.realizationWeakEquivalences (nerveMap
      ((ULift.downFunctor.{u,u,u+1} ⋙ ULiftHom.down.{0,u,u} ⋙
        reedyIntoFibrantGadgetInputs K) ⋙ fibrantInputInclusion K)) := by
  rw [← nerveMap_comp]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (reedyFibrantInputs_liftedNerve_weak K)
    (fibrantInputInclusion_nerve_weak_of_quasicategory K)

end CategoryTheory.CoherentRealization.OriginalGadgetComparison
