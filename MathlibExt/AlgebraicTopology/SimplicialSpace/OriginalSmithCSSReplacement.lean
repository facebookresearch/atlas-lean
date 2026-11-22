/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalDerivedMapping
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.LocalizerDesignation

/-!
# Functorial Smith replacement by complete Segal spaces

The Smith replacement for the full spine and completeness family is transported to simplicial
spaces through the raw and designated carrier equivalence. Its value is a complete Segal space
at every input, its natural unit is a Rezk weak equivalence, and its action preserves Rezk weak
equivalences.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace.OriginalSmithCSS
open SimplicialPresheaf.OriginalLocalDerived

/-- The original Smith R for the literal Rezk spine/completeness family,
transported through the actual raw/designated carrier equivalence. -/
def replacement : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  forget ⋙ localR SSet.Rezk.localizingMap.{u} ⋙ ofSimplicialObject

/-- The actual first leg of the stored Smith second factorization. -/
def unit : 𝟭 SimplicialSpace.{u} ⟶ replacement where
  app W := ofSimplicialObject.map ((localRUnit SSet.Rezk.localizingMap.{u}).app W.diagram)
  naturality W V f := by
    apply InducedCategory.hom_ext
    change f.hom ≫ (localRUnit SSet.Rezk.localizingMap.{u}).app V.diagram =
      (localRUnit SSet.Rezk.localizingMap.{u}).app W.diagram ≫
        (localR SSet.Rezk.localizingMap.{u}).map f.hom
    exact (localRUnit SSet.Rezk.localizingMap.{u}).naturality f.hom

theorem replacement_diagram (W : SimplicialSpace.{u}) :
    (replacement.obj W).diagram = (localR SSet.Rezk.localizingMap.{u}).obj W.diagram := rfl

theorem unit_hom (W : SimplicialSpace.{u}) :
    (unit.app W).hom = (localRUnit SSet.Rezk.localizingMap.{u}).app W.diagram := rfl

/-- Global Smith RLP gives the actual complete-Segal target at every object. -/
theorem replacement_completeSegal (W : SimplicialSpace.{u}) :
    completeSegalSpaces (replacement.obj W) :=
  (SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalFibrant_iff_completeSegalSpaces
    ((localR SSet.Rezk.localizingMap.{u}).obj W.diagram)).mp
      (localR_isOriginalLocalFibrant SSet.Rezk.localizingMap.{u} W.diagram)

/-- The stored Smith unit belongs to the original all-complete-target weak class. -/
theorem unit_rezkWeak (W : SimplicialSpace.{u}) : rezkWeakEquivalences (unit.app W) :=
  (SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak
    ((localRUnit SSet.Rezk.localizingMap.{u}).app W.diagram)).mp
      (localRUnit_localTrivialCofibration SSet.Rezk.localizingMap.{u} W.diagram).2

/-- The actual Smith action preserves the same global Rezk weak class. -/
theorem replacement_map_rezkWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hf : rezkWeakEquivalences f) : rezkWeakEquivalences (replacement.map f) :=
  (SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak
    ((localR SSet.Rezk.localizingMap.{u}).map f.hom)).mp
      (localR_map_localWeak SSet.Rezk.localizingMap.{u} f.hom
        ((SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak f.hom).mpr hf))

/-- Both characteristic naturality squares use the original object maps. -/
theorem unit_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ unit.app V = unit.app W ≫ replacement.map f := unit.naturality f

end SimplicialSpace.OriginalSmithCSS
