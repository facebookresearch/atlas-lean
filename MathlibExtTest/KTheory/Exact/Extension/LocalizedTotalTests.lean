/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedTotal
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-!
# Consumers of the original localized-total extension API

The actual unit inclusion factors through the literal denominator-unit
fiber. Represented lifts retain the given denominator and original positive
row. The realized comma and terminal comparisons use the same original
extension spaces, with independent object and Hom universes.

An all-ring instance checks the localized-total contraction in the exact
category of finite projective modules over an associative unital ring.
-/

universe u v uRing vModule

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory
open scoped Simplicial MonoidalCategory CategoryTheory.Limits.CoreBiprodMonoidal
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace MathlibExtTest.LocalizedTotal

section ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] diagonalAction

/-- The derived denominator instance and original unit inclusion give an
actual strict-fibre functor, whose total inclusion is the original map. -/
theorem original_unit_inclusion_factors_through_strict_fibre :
    (AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C)).IsCofibered ∧
      ∃ J : ExtensionCategory C ⥤
          Functor.Fiber (AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C))
            (⟨𝟙_ (Core C)⟩ : MonoidalActionCategory (Core C) (Core C)),
        J ⋙ Functor.Fiber.fiberInclusion =
          AlgebraicKTheory.LocalizedTotal.positiveInclusion (C := C) := by
  let p := AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C)
  let I := AlgebraicKTheory.LocalizedTotal.positiveInclusion (C := C)
  let d : MonoidalActionCategory (Core C) (Core C) := ⟨𝟙_ (Core C)⟩
  have hCof : p.IsCofibered :=
    denominatorProjection_isCofibered (C := C) (X := ExtensionCategory C)
  have hConst : I ⋙ p = (Functor.const (ExtensionCategory C)).obj d := by
    exact CategoryTheory.Functor.hext
      (fun E => AlgebraicKTheory.LocalizedTotal.positiveInclusion_denominator_obj (C := C) E)
      (fun _ _ f => by
        dsimp only [p, I, d]
        simpa only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map, AlgebraicKTheory.LocalizedTotal.positiveInclusion_denominator_obj]
          using (heq_of_eq
            (AlgebraicKTheory.LocalizedTotal.positiveInclusion_denominator_map f)))
  let J := Functor.Fiber.inducedFunctor hConst
  exact ⟨hCof, J, Functor.Fiber.inducedFunctor_comp hConst⟩

/-- At an arbitrary original denominator, the constructed cocartesian lift
keeps the given target and the complete original represented base arrow. -/
theorem represented_extension_lift_keeps_row_and_denominator
    (a : ExtensionCategory.localizedExtensions (C := C)) (s : Core C)
    (r : RawHom (denominatorObject a)
      (⟨s⟩ : MonoidalActionCategory (Core C) (Core C))) :
    let z := denominatorLiftObject a r
    let phi : a ⟶ z := MonoidalActionCategory.Hom.mk (denominatorLiftRaw a r)
    z.of = (r.stabilizer ⊙ₗ a.of.1, s) ∧
      (AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C)).map phi =
        MonoidalActionCategory.Hom.mk r ∧
      Functor.IsStronglyCocartesian (AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C))
        (MonoidalActionCategory.Hom.mk r) phi := by
  let phi := MonoidalActionCategory.Hom.mk (denominatorLiftRaw a r)
  have hMap : (AlgebraicKTheory.LocalizedTotal.denominatorFunctor (C := C)).map phi =
      MonoidalActionCategory.Hom.mk r :=
    (denominatorProjection_map_mk (denominatorLiftRaw a r)).trans
      (congrArg MonoidalActionCategory.Hom.mk (denominatorLiftRaw_projection a r))
  exact ⟨rfl, hMap, denominatorLift_isStronglyCocartesian a r⟩

/-- The final adapter keeps the literal localized-total terminal map as its
forward map and contracts that original realization without a CW premise. -/
theorem literal_terminal_forward_map_and_original_contraction :
    let N : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
    let q : N ⟶ (⊤_ SSet.{max u v}) := terminal.from N
    ContractibleSpace (SSet.toTop.obj N) ∧
      ∃ (_hq : SSet.realizationWeakEquivalences q)
        (E : ContinuousMap.HomotopyEquiv (SSet.toTop.obj N)
          (SSet.toTop.obj (⊤_ SSet.{max u v}))),
        E.toFun = (SSet.toTop.map q).hom ∧
          Nonempty (ContinuousMap.Homotopy
            (E.invFun.comp (SSet.toTop.map q).hom)
            (ContinuousMap.id (SSet.toTop.obj N))) := by
  let N : SSet.{max u v} := nerve (ExtensionCategory.localizedExtensions (C := C))
  let q : N ⟶ (⊤_ SSet.{max u v}) := terminal.from N
  have hq : SSet.realizationWeakEquivalences q :=
    AlgebraicKTheory.LocalizedTotal.localizedTotal_to_terminal_mem (C := C)
  let E := SSet.RealizationCWUpgrade.realizationHomotopyEquiv q hq
  have hForward : E.toFun = (SSet.toTop.map q).hom :=
    SSet.RealizationCWUpgrade.realizationHomotopyEquiv_toFun q hq
  refine ⟨AlgebraicKTheory.LocalizedTotal.localizedTotal_contractible (C := C),
    hq, E, hForward, ?_⟩
  rcases E.left_inv with ⟨H⟩
  refine ⟨?_⟩
  simpa only [hForward] using H

end ExactCategory

/-- Every associative unital ring supplies the actual projective exact
category instance and the same original localized-total contraction. -/
theorem allRing_original_localized_total_contractible
    {R : Type uRing} [Ring R] :
    ContractibleSpace
      (SSet.toTop.obj
        (nerve (ExtensionCategory.localizedExtensions
          (C := FGProjectiveCat.{vModule} R)) :
            SSet.{max uRing (vModule + 1)})) := by
  exact AlgebraicKTheory.LocalizedTotal.localizedTotal_contractible
    (C := FGProjectiveCat.{vModule} R)

end MathlibExtTest.LocalizedTotal

end
