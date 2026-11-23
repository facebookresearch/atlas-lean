/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberSelectedPoint

/-!
# Actual completed-unit coordinates and the entire original fiber path

The selected point is the positive image of the Core zero object. The original
zero-row functor gives its strict-fiber total object; the actual K comparison
keeps that coordinate and its full constant Q path. The ring case derives
comparison weakness from the original auxiliary bases, rather than supplying it.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite AlgebraicKTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

namespace MathlibExtTest.OriginalQZeroSelectedPoint

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The actual zero pair, strict target, total image and whole carried path agree at the unit. -/
theorem actual_completed_unit_full_fiber_coordinates :
    let a : SInverse (Core C) (Core C) :=
      (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
    let b : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
      (FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)
    let p := SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
    let q := SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
      (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))
    let z := OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)
      (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a))
    a.toProd = ((⟨(0 : C)⟩ : Core C), (⟨(0 : C)⟩ : Core C)) ∧
      (ExtensionCategory.localizedTarget (C := C)).obj b.val = (⟨0⟩ : QuillenQ C) ∧
      TopCat.homotopyFiberToTotal p q z =
        SSet.realizedVertex
          (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ b.val) ∧
      TopCat.homotopyFiberPath p q z = ContinuousMap.const TopCat.I.{max u v} q := by
  dsimp only
  let a : SInverse (Core C) (Core C) :=
    (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  let b : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
    (FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
      ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)
  refine ⟨SInverse.inclusion_obj (Core C) (Core C) (𝟙_ (Core C)), b.property, ?_,
    OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_path_eq_const
      (C := C)⟩
  have hForget : b.val =
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedForget (C := C) (0 : C)).obj a := by
    change (FixedTargetExtension.localizedFiberForget (C := C) (0 : C)).obj
        ((FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
          ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)) =
      (FixedTargetExtension.localizedForget (C := C) (0 : C)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)
    exact congrArg
      (fun T : FixedTargetExtension.localizedRows (C := C) (0 : C) ⥤
          ExtensionCategory.localizedExtensions (C := C) =>
        T.obj ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a))
      (FixedTargetExtension.localizedFiberFunctor_forget (C := C) (X := (0 : C)))
  have hTotal :=
    OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_toTotal (C := C)
  exact hTotal.trans (congrArg
    (fun x : ExtensionCategory.localizedExtensions (C := C) =>
      SSet.realizedVertex
        (X := (nerve (ExtensionCategory.localizedExtensions (C := C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ x)) hForget.symm)

/-- Arbitrary ring/module levels retain the original weak map and every unit-path time. -/
theorem projective_unit_path_with_derived_comparison_weakness
    {R : Type uRing} [Ring R] (t : TopCat.I.{max uRing (vModule + 1)}) :
    let C0 := FGProjectiveCat.{vModule} R
    let a : SInverse (Core C0) (Core C0) :=
      (SInverse.inclusion (Core C0) (Core C0)).obj (𝟙_ (Core C0))
    let p := SSet.toTop.map
      (nerveMapCommonHom.{max uRing (vModule + 1), max uRing (vModule + 1), 0}
        (ExtensionCategory.localizedTarget (C := C0)))
    let q := SSet.realizedVertex
      (X := (nerve (QuillenQ C0) : SSet.{max uRing (vModule + 1)}))
      (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C0))
    TopCat.weakHomotopyEquivalences
        (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C0)) ∧
      TopCat.homotopyFiberPath p q
        (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C0)
          (SSet.realizedVertex
            (X := (nerve (SInverse (Core C0) (Core C0)) :
              SSet.{max uRing (vModule + 1)}))
            (ComposableArrows.mk₀ a))) t = q := by
  dsimp only
  exact ⟨OriginalQZeroComparison.projectiveCompletedCoreToOriginalHomotopyFiber_mem,
    OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_path_apply
      (C := FGProjectiveCat.{vModule} R) t⟩

end MathlibExtTest.OriginalQZeroSelectedPoint

namespace AlgebraicKTheory.OriginalQZeroComparison

#print axioms completedCoreToZeroLeftCommaNerveMap_vertex
#print axioms completedCoreUnitLeftComma_hom_eqToHom
#print axioms completedCoreToOriginalHomotopyFiber_unit_path_apply
#print axioms completedCoreToOriginalHomotopyFiber_unit_path_eq_const

end AlgebraicKTheory.OriginalQZeroComparison

namespace MathlibExtTest.OriginalQZeroSelectedPoint

#print axioms actual_completed_unit_full_fiber_coordinates
#print axioms projective_unit_path_with_derived_comparison_weakness

end MathlibExtTest.OriginalQZeroSelectedPoint

end
