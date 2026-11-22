/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectFibre
import MathlibExt.AlgebraicTopology.SimplicialObject.ExtraDegeneracyPointBaseChange
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopyRealization
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# The actual fixed-object left-decalage diagram has a weak point augmentation

The original decalage extra degeneracy pulls back to the same fixed
object. At each original inner degree it gives the whole actual row
augmentation as a weak map. The original diagonal theorem proves that
the complete fixed-object path diagram has its actual weak augmentation
to the same original point, without fibrancy or Segal assumptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The complete original fixed-object path diagram, with its original point augmentation. -/
def augmented (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SimplicialObject.Augmented SSet.{u} :=
  SimplicialObject.Augmented.ExtraDegeneracy.baseChange
    (CategoryTheory.SimplicialObject.LeftDecalage.augmented W.diagram) (SSet.yonedaEquiv.symm x)

/-- The whole original fixed-object path pullback retains its actual induced extra degeneracy. -/
def extraDegeneracy (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (augmented W x).ExtraDegeneracy :=
  SimplicialObject.Augmented.ExtraDegeneracy.baseChangeExtraDegeneracy
    (C := SSet.{u}) (A := CategoryTheory.SimplicialObject.LeftDecalage.augmented W.diagram)
    (ed := CategoryTheory.SimplicialObject.LeftDecalage.extraDegeneracy W.diagram)
    (p := SSet.yonedaEquiv.symm x)

/-- The actual full fixed-object path diagonal retains its literal original point map. -/
def diagonalAugmentation (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.obj (diagram W x) ⟶ (Δ[0] : SSet.{u}) :=
  SSet.simplicialDiagonalFunctor.map (toPoint W x) ≫ (SSet.diagonalConstIso (Δ[0] : SSet.{u})).hom

/-- The complete original fixed-object path diagram has an actual weak point augmentation. -/
theorem diagonalAugmentation_weak (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (diagonalAugmentation W x) := by
  have h : SSet.realizationWeakEquivalences (SSet.simplicialDiagonalFunctor.map (toPoint W x)) := by
    apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    intro n
    let ed := (extraDegeneracy W x).map (SSet.evaluation.obj (op (SimplexCategory.mk n)))
    exact ed.hom_mem_realizationWeakEquivalences
  exact SSet.realizationWeakEquivalences.comp_mem _ _ h
    (SSet.realizationWeakEquivalences.of_isIso _)

end SimplicialSpace.LeftDecalageObject
