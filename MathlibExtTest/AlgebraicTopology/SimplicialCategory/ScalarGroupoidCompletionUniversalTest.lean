/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionUniversal
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment

/-! # The completion's universal property into a concrete scalar-groupoid target

A codiscrete carrier has the point as every Hom, so each of its scalar categories is a
groupoid. Enriched maps from the groupoid completion of a carrier into it correspond,
by `homEquiv`, to enriched maps from the carrier itself. On objects both directions
keep the original object function; for the codiscrete carrier on `Bool` the inverse of
the map induced by negation sends `true` to `false`.
-/

noncomputable section
universe u
open CategoryTheory
open CategoryTheory.SimplicialEnrichment

namespace ScalarGroupoidCompletionUniversalTest

/-- Every scalar category of a codiscrete carrier is a groupoid: all its Hom sets are points. -/
instance isGroupoid_codiscrete (O : Type u) (q : SimplexCategoryᵒᵖ) :
    IsGroupoid (SSet.ScalarObject (CodiscreteEnrichment.object O) q) where
  all_isIso _ := ⟨⟨(PUnit.unit : PUnit.{u + 1}), Subsingleton.elim (α := PUnit.{u + 1}) _ _,
    Subsingleton.elim (α := PUnit.{u + 1}) _ _⟩⟩

variable {C : Carrier.{u}} {O : Type u}

/-- The forward direction is restriction along the unit, which keeps every object. -/
theorem homEquiv_obj (H : ScalarGroupoidCompletion.object C ⟶ CodiscreteEnrichment.object O)
    (x : C) : (ScalarGroupoidCompletion.homEquiv H).obj x = H.obj x := rfl

/-- The inverse direction extends a map from the carrier without changing objects. -/
theorem homEquiv_symm_obj (F : C ⟶ CodiscreteEnrichment.object O) (x : C) :
    (ScalarGroupoidCompletion.homEquiv.symm F).obj x = F.obj x := rfl

/-- Two maps out of the completion with the same restriction along the unit are equal. -/
theorem ext_of_unit (H K : ScalarGroupoidCompletion.object C ⟶ CodiscreteEnrichment.object O)
    (h : ScalarGroupoidCompletion.unit C ≫ H = ScalarGroupoidCompletion.unit C ≫ K) : H = K :=
  ScalarGroupoidCompletion.unit_restriction_injective h

/-- Maps from the completion into a codiscrete carrier are exactly object functions. -/
def objectFunctions :
    (ScalarGroupoidCompletion.object C ⟶ CodiscreteEnrichment.object O) ≃ ((C : Type u) ⟶ O) :=
  ScalarGroupoidCompletion.homEquiv.trans (CodiscreteEnrichment.homEquiv C O)

/-- The codiscrete carrier on `Bool`. -/
abbrev bools : Carrier.{0} := CodiscreteEnrichment.object Bool

/-- The enriched map of `bools` induced by negation. -/
def negation : bools ⟶ bools := CodiscreteEnrichment.extend bools Bool (↾not)

/-- The inverse of `homEquiv` really moves objects: negation is extended to the completion. -/
theorem homEquiv_symm_negation_obj (x : Bool) :
    (ScalarGroupoidCompletion.homEquiv.symm negation).obj x = !x := rfl

/-- Restricting the extended negation along the unit recovers negation. -/
theorem homEquiv_homEquiv_symm_negation :
    ScalarGroupoidCompletion.homEquiv (ScalarGroupoidCompletion.homEquiv.symm negation) =
      negation :=
  ScalarGroupoidCompletion.homEquiv.apply_symm_apply negation

/-- The extension of negation differs from the extension of the identity. -/
theorem homEquiv_symm_negation_ne :
    ScalarGroupoidCompletion.homEquiv.symm negation ≠
      ScalarGroupoidCompletion.homEquiv.symm (𝟙 bools) := by
  intro h
  have := congrArg (fun H : ScalarGroupoidCompletion.object bools ⟶ bools => H.obj true) h
  exact Bool.false_ne_true this

/-- Boundary case: over the empty carrier there is exactly one map out of the completion. -/
instance (O : Type) :
    Unique (ScalarGroupoidCompletion.object (CodiscreteEnrichment.object PEmpty) ⟶
      CodiscreteEnrichment.object O) :=
  (objectFunctions.trans
    { toFun := fun f => (f : PEmpty → O)
      invFun := fun f => ↾f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).unique

end ScalarGroupoidCompletionUniversalTest
