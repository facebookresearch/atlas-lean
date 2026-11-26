/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallLimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Varying-object carrier limits at a raised universe

The small-limit instances apply to `Carrier.{u + 1}` with indexing shapes in `Type 0`.
For a product of two codiscrete carriers with different object types (two and three
objects), the product's objects are exactly the pairs of objects, read back through the
two projections. The empty limit has exactly one object.
-/

noncomputable section
universe u
open CategoryTheory Limits
open CategoryTheory.SimplicialEnrichment

namespace CarrierSmallLimitsTest

/-- All small limits exist one universe up. -/
example : HasLimitsOfSize.{u + 1, u + 1} Carrier.{u + 1} := inferInstance

/-- A shape from `Type 0` has limits in the raised carrier category. -/
example : HasLimitsOfShape (Discrete WalkingPair) Carrier.{u + 1} := inferInstance

/-- Object forgetting preserves those limits. -/
example : PreservesLimitsOfShape (Discrete WalkingPair) forgetObjects.{u + 1} := inferInstance

/-- Two codiscrete carriers whose object types differ. -/
abbrev left : Carrier.{u + 1} := CodiscreteEnrichment.object (ULift.{u + 1} Bool)

/-- The second carrier, with three objects. -/
abbrev right : Carrier.{u + 1} := CodiscreteEnrichment.object (ULift.{u + 1} (Fin 3))

/-- The objects of the enriched product are the pairs of objects. -/
def productObjects :
    forgetObjects.obj (left.{u} ⨯ right.{u}) ≃ ULift.{u + 1} Bool × ULift.{u + 1} (Fin 3) :=
  ((PreservesLimitPair.iso forgetObjects left right) ≪≫
    Types.binaryProductIso (ULift.{u + 1} Bool) (ULift.{u + 1} (Fin 3))).toEquiv

/-- Reading an object back from a pair: its first projection is the first coordinate. -/
theorem fst_productObjects_symm (p : ULift.{u + 1} Bool × ULift.{u + 1} (Fin 3)) :
    (prod.fst : left.{u} ⨯ right.{u} ⟶ left).obj (productObjects.symm p) = p.1 := by
  have h := PreservesLimitPair.iso_inv_fst forgetObjects.{u + 1} left right
  exact (congrArg (fun g => g ((Types.binaryProductIso _ _).inv p)) h).trans
    (Types.binaryProductIso_inv_comp_fst_apply _ _ p)

/-- Its second projection is the second coordinate. -/
theorem snd_productObjects_symm (p : ULift.{u + 1} Bool × ULift.{u + 1} (Fin 3)) :
    (prod.snd : left.{u} ⨯ right.{u} ⟶ right).obj (productObjects.symm p) = p.2 := by
  have h := PreservesLimitPair.iso_inv_snd forgetObjects.{u + 1} left right
  exact (congrArg (fun g => g ((Types.binaryProductIso _ _).inv p)) h).trans
    (Types.binaryProductIso_inv_comp_snd_apply _ _ p)

/-- A concrete object of the product, projecting to different objects of the two factors. -/
example : (prod.fst : left.{u} ⨯ right.{u} ⟶ left).obj (productObjects.symm (⟨true⟩, ⟨2⟩)) =
      ⟨true⟩ ∧
    (prod.snd : left.{u} ⨯ right.{u} ⟶ right).obj (productObjects.symm (⟨true⟩, ⟨2⟩)) = ⟨2⟩ :=
  ⟨fst_productObjects_symm _, snd_productObjects_symm _⟩

/-- Boundary case: the empty limit has exactly one object. -/
def terminalObjects : forgetObjects.{u + 1}.obj (⊤_ Carrier.{u + 1}) ≃ PUnit.{u + 2} :=
  ((PreservesTerminal.iso forgetObjects.{u + 1}) ≪≫ Types.terminalIso.{u + 1}).toEquiv

instance : Unique (forgetObjects.{u + 1}.obj (⊤_ Carrier.{u + 1})) := terminalObjects.unique

end CarrierSmallLimitsTest
