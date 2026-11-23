/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization.DenominatorCommaRealization

/-!
# Direction of the actual realized denominator comma comparison

These tests concern the original comparison maps and their composites.
No homotopy-equivalence, adjunction or fiber result is supplied as a premise.
-/

@[expose] public section

universe u v uX vX

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalActionCategory
open scoped MonoidalCategory CategoryTheory.MonoidalCategory.MonoidalLeftAction
open scoped CategoryTheory.Limits.CoreBiprodMonoidal

namespace CategoryTheory.ActionDenominatorRealizationConsumers

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {X : Type uX} [Category.{vX} X] [MonoidalLeftAction (Core C) X]

attribute [local instance] diagonalAction

/-- Retraction followed by inclusion is homotopic to the original comma
identity, in the continuous-map composition order used by the comparison. -/
theorem realized_retraction_then_inclusion (s : Core C) :
    Nonempty (ContinuousMap.Homotopy
      ((SSet.toTop.map
        (nerveMapCommonHomUp.{max u uX, max u v, vX}
          (denominatorCommaInclusion (X := X) s))).hom.comp
        (SSet.toTop.map
        (nerveMapCommonHom.{max u uX, max u v, vX}
          (denominatorCommaRetraction (X := X) s))).hom)
      (ContinuousMap.id
        (SSet.toTop.obj (nerve (CostructuredArrow (denominatorProjection (Core C) X)
          (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) : SSet.{max u v uX vX})))) := by
  exact (denominatorCommaRealizedHomotopyEquiv (X := X) s).left_inv

/-- Inclusion followed by retraction is homotopic to the original strict
fiber identity at the same given denominator. -/
theorem realized_inclusion_then_retraction (s : Core C) :
    Nonempty (ContinuousMap.Homotopy
      ((SSet.toTop.map
        (nerveMapCommonHom.{max u uX, max u v, vX}
          (denominatorCommaRetraction (X := X) s))).hom.comp
        (SSet.toTop.map
        (nerveMapCommonHomUp.{max u uX, max u v, vX}
          (denominatorCommaInclusion (X := X) s))).hom)
      (ContinuousMap.id
        (SSet.toTop.obj (nerve (denominatorFiber (X := X) s) : SSet.{max u v uX vX})))) := by
  exact (denominatorCommaRealizedHomotopyEquiv (X := X) s).right_inv

end General

section LargerActedUniverse

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  {Y : Type (max u v + 1)} [Category.{max u v + 1} Y]
  [MonoidalLeftAction (Core C) Y]

attribute [local instance] diagonalAction

/-- With an acted-on category strictly above the actor's object/Hom maximum,
the original fixed-denominator functor survives the comma/inclusion round trip. -/
theorem larger_acted_universe_positive_comma_round_trip (s : Core C) :
    let Q := denominatorFiberFunctor (X := Y) s
    let L := denominatorCommaRetraction (X := Y) s
    let R := denominatorCommaInclusion (X := Y) s
    Q ⋙ (CategoryTheory.Functor.Fiber.fiberInclusion :
        denominatorFiber (X := Y) s ⥤ SInverse (Core C) Y) =
        fixedDenominatorTotal (X := Y) s ∧
      Nonempty (ContinuousMap.Homotopy
        ((SSet.toTop.map
          (nerveMapCommonHom.{max u v + 1, max u v, max u v + 1} L)).hom.comp
          ((SSet.toTop.map
            (nerveMapCommonHomUp.{max u v + 1, max u v, max u v + 1} R)).hom.comp
            (SSet.toTop.map (nerveMap Q)).hom))
        (SSet.toTop.map (nerveMap Q)).hom) := by
  dsimp only
  let Q := denominatorFiberFunctor (X := Y) s
  let i := (SSet.toTop.map (nerveMap Q)).hom
  let e := denominatorCommaRealizedHomotopyEquiv (X := Y) s
  constructor
  · exact denominatorFiberFunctor_forget (X := Y) s
  · let H := Classical.choice e.right_inv
    have hForward := denominatorCommaRealizedHomotopyEquiv_toFun (X := Y) s
    have hInverse := denominatorCommaRealizedHomotopyEquiv_invFun (X := Y) s
    refine ⟨(H.compContinuousMap i).cast ?_ ?_⟩
    · simp only [Q, e, i, hForward, hInverse, ContinuousMap.comp_assoc]
    · exact ContinuousMap.id_comp i

end LargerActedUniverse

end CategoryTheory.ActionDenominatorRealizationConsumers

end
