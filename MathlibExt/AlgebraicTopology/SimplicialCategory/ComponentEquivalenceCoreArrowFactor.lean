/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators

/-!
# The SAME original supplied equivalence arrow factors through its full core

The actual original component-equivalence vertex and its entire original
unit-Hom coefficient map land in the SAME full core Hom. Both original
walking-arrow object images are retained literally. Its full enriched
factor followed by the actual core inclusion is exactly the supplied
original walking-arrow functor. No countable interval or weak outcome
is inferred from this original core factorization.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

variable {C : Carrier.{u}} {x y : C}

/-- The SAME supplied original equivalence vertex is retained in its actual full core Hom. -/
def selectedVertex (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    (hom C x y) _⦋0⦌ := ⟨e, (hom_zero_iff C x y e).mpr he⟩

/-- The SAME full original unit-Hom coefficient lifts to the actual selected Hom, retaining every original scalar
operator. -/
def selectedUnit (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    𝟙_ SSet.{u} ⟶ hom C x y := (SSet.unitHomEquiv _).symm (selectedVertex e he)

/-- The full original scalar coefficient readback is the SAME supplied original unit-Hom map. -/
theorem selectedUnit_inclusion (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    selectedUnit e he ≫ inclusionHom C x y = (SSet.unitHomEquiv _).symm e := by
  apply (SSet.unitHomEquiv _).injective
  exact (congrArg Subtype.val ((SSet.unitHomEquiv (hom C x y)).apply_symm_apply (selectedVertex e he))).trans
    ((SSet.unitHomEquiv (x ⟶[SSet.{u}] y)).apply_symm_apply e).symm

/-- The entire original supplied walking-arrow coefficient factors through the SAME full actual original core. -/
def arrowFactor (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    BergnerTwoObject.object (𝟙_ SSet.{u}) ⟶ object C := BergnerTwoObject.ofMap x y (selectedUnit e he)

/-- The actual original source and target labels remain exactly the two supplied original objects. -/
theorem arrowFactor_endpoints (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    (arrowFactor e he).obj (BergnerTwoObject.source _) = x ∧
      (arrowFactor e he).obj (BergnerTwoObject.target _) = y := ⟨rfl, rfl⟩

/-- The SAME full original walking-arrow map is recovered by the genuine core factor and its entire original
inclusion. -/
theorem arrowFactor_inclusion (e : (x ⟶[SSet.{u}] y) _⦋0⦌) (he : IsIso (ComponentCategory.arrowOf C e)) :
    arrowFactor e he ≫ inclusion C =
      BergnerTwoObject.ofMap x y ((SSet.unitHomEquiv _).symm e) :=
  (BergnerTwoObject.ofMap_comp (C := object C) (D := C) x y (selectedUnit e he) (inclusion C)).trans
    (congrArg (BergnerTwoObject.ofMap (C := C) x y) (selectedUnit_inclusion e he))

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
