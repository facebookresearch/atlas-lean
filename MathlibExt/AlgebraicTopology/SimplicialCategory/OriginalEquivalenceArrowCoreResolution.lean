/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeSingleHomCofibrant
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreCofibrantResolution

/-!
# The supplied original equivalence arrow lifts into the genuine core resolution

The actual original equivalence vertex defines its same full coefficient
map into the component-equivalence core. The genuine original free
single-Hom source is cofibrant, so it lifts through the SAME original
boundary resolution. The actual whole factor recovers the supplied
coefficient, both original objects and their literal target vertex.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalEquivalenceArrowCoreResolution
open FixedObjects ComponentEquivalenceCore
variable {C : Carrier.{u}} (x y : C)

/-- The full original walking-arrow source on the SAME original object labels. -/
abbrev source : FixedObjects C := FreeSingleHom.object x y (𝟙_ SSet.{u})

/-- The supplied original equivalence gives its SAME full coefficient map to the actual original core. -/
def toCore (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    source x y ⟶ fixedTarget C :=
  FreeSingleHom.extend x y (𝟙_ SSet.{u}) (fixedTarget C) (selectedUnit e he)

/-- The actual lift square uses the SAME original initial map and core resolution projection. -/
theorem liftSquare (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    CommSq (initial.to (resolvedFixedObject C)) (initial.to (source x y))
      (resolutionRight C) (toCore x y e he) :=
  ⟨initialIsInitial.hom_ext _ _⟩

/-- Construct the SAME whole original walking-arrow lift through the actual boundary resolution. -/
def toResolution (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    source x y ⟶ resolvedFixedObject C := by
  let _ : ModelCategory (FixedObjects C) := FixedObjectModel.modelCategory C
  let _ : IsCofibrant (source x y) := FreeSingleHom.isCofibrant x y (𝟙_ SSet.{u})
  have hcof : FixedObjectModel.cofibrations C (initial.to (source x y)) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (initial.to (source x y))).mp
      (inferInstance : Cofibration (initial.to (source x y)))
  let _ : HasLiftingProperty (initial.to (source x y)) (resolutionRight C) :=
    hcof _ (resolution C).hp
  exact (liftSquare x y e he).lift

/-- The SAME whole original core projection recovers the entire supplied walking-arrow core map. -/
theorem toResolution_projection (e : (x ⟶[SSet.{u}] y) _⦋0⦌)
    (he : IsIso (ComponentCategory.arrowOf C e)) :
    toResolution x y e he ≫ resolutionRight C = toCore x y e he := by
  let _ : ModelCategory (FixedObjects C) := FixedObjectModel.modelCategory C
  let _ : IsCofibrant (source x y) := FreeSingleHom.isCofibrant x y (𝟙_ SSet.{u})
  have hcof : FixedObjectModel.cofibrations C (initial.to (source x y)) :=
    (FixedObjectModel.cofibration_iff_freeBoundary (initial.to (source x y))).mp
      (inferInstance : Cofibration (initial.to (source x y)))
  let _ : HasLiftingProperty (initial.to (source x y)) (resolutionRight C) := hcof _ (resolution C).hp
  exact (liftSquare x y e he).fac_right

/-- The actual lifted full generator retains the SAME original selected unit coefficient. -/
theorem generator_projection (e : (x ⟶[SSet.{u}] y) _⦋0⦌)
    (he : IsIso (ComponentCategory.arrowOf C e)) :
    FreeSingleHom.generator x y (𝟙_ SSet.{u}) ≫
      homMap (toResolution x y e he) x y ≫ homMap (resolutionRight C) x y = selectedUnit e he := by
  have h := congrArg (fun F => FreeSingleHom.generator x y (𝟙_ SSet.{u}) ≫ homMap F x y)
    (toResolution_projection x y e he)
  have hc := homMap_comp (toResolution x y e he) (resolutionRight C) x y
  have h' := (congrArg (fun F => FreeSingleHom.generator x y (𝟙_ SSet.{u}) ≫ F) hc).symm.trans h
  exact (Category.assoc _ _ _).trans
    (h'.trans (FreeSingleHom.restrict_extend x y (𝟙_ SSet.{u}) (fixedTarget C) (selectedUnit e he)))

/-- The SAME full original generator readback recovers the literal supplied equivalence coefficient in C. -/
theorem generator_original (e : (x ⟶[SSet.{u}] y) _⦋0⦌)
    (he : IsIso (ComponentCategory.arrowOf C e)) :
    FreeSingleHom.generator x y (𝟙_ SSet.{u}) ≫ homMap (toResolution x y e he) x y ≫
      homMap (resolutionRight C) x y ≫ inclusionHom C x y = (SSet.unitHomEquiv _).symm e := by
  have h := congrArg (fun f => f ≫ inclusionHom C x y) (generator_projection x y e he)
  exact (Category.assoc _ _ _).symm.trans (h.trans (selectedUnit_inclusion e he))

end CategoryTheory.SimplicialEnrichment.OriginalEquivalenceArrowCoreResolution
