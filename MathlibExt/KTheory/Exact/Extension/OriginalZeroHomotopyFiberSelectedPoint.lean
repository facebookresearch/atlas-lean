/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberComparison

/-!
# The original completed-core vertices in the zero left comma

The actual up nerve map and Cartesian inclusion carry every core pair to its
original strict-zero-fiber object. At the completed unit, the defining comma
arrow is the inverse stored fiber equality. These statements retain the original
unit, denominators and object/Hom levels without selecting a new path.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Every actual core-pair vertex is carried to its original strict-fiber comma vertex. -/
theorem completedCoreToZeroLeftCommaNerveMap_vertex (a : SInverse (Core C) (Core C)) :
    SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))
        (SSet.realizedVertex
          (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
          (ComposableArrows.mk₀ a)) =
      SSet.realizedVertex
        (X := (nerve (StructuredArrow (⟨0⟩ : QuillenQ C)
          (ExtensionCategory.localizedTarget (C := C))) : SSet.{max u v}))
        (ComposableArrows.mk₀
          ((Functor.fiberToStructuredArrow
              (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)).obj
            ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
              FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj a))) := by
  let theta := FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
    FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)
  let j := Functor.fiberToStructuredArrow
    (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)
  have hApp : (completedCoreToZeroLeftCommaNerveMap (C := C)).app (op ⦋0⦌)
      (ComposableArrows.mk₀ a) = ComposableArrows.mk₀ (j.obj (theta.obj a)) := by
    change (nerveMap j).app (op ⦋0⦌)
        ((nerveMapCommonHomUp.{u, max u v, 0} theta).app (op ⦋0⦌)
          (ComposableArrows.mk₀ a)) = ComposableArrows.mk₀ (j.obj (theta.obj a))
    have h0 :
        ((nerveMap j).app (op ⦋0⦌)
          ((nerveMapCommonHomUp.{u, max u v, 0} theta).app (op ⦋0⦌)
            (ComposableArrows.mk₀ a)) :
              (nerve (StructuredArrow (⟨0⟩ : QuillenQ C)
                (ExtensionCategory.localizedTarget (C := C))) : SSet.{max u v}) _⦋0⦌) =
        (nerveMap j).app (op ⦋0⦌) (ComposableArrows.mk₀ (theta.obj a)) :=
      congrArg
        (fun x : (nerve (FixedTargetExtension.localizedFiber (C := C) (0 : C)) :
            SSet.{max u v}) _⦋0⦌ => (nerveMap j).app (op ⦋0⦌) x)
        (nerveMapCommonHomUp_app_mk₀.{u, max u v, 0} theta a)
    have h1 :
        ((nerveMap j).app (op ⦋0⦌) (ComposableArrows.mk₀ (theta.obj a)) :
          (nerve (StructuredArrow (⟨0⟩ : QuillenQ C)
            (ExtensionCategory.localizedTarget (C := C))) : SSet.{max u v}) _⦋0⦌) =
        ComposableArrows.mk₀ (j.obj (theta.obj a)) := ComposableArrows.ext₀ rfl
    exact h0.trans h1
  have h := SSet.realizedVertex_naturality
    (completedCoreToZeroLeftCommaNerveMap (C := C)) (ComposableArrows.mk₀ a)
  exact h.symm.trans (congrArg (fun x => SSet.realizedVertex x) hApp)

/-- The original unit's comma arrow is exactly the inverse strict-fiber equality. -/
theorem completedCoreUnitLeftComma_hom_eqToHom :
    let b : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
      (FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
        ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj
          ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))
    ((Functor.fiberToStructuredArrow
        (p := ExtensionCategory.localizedTarget (C := C)) (⟨0⟩ : QuillenQ C)).obj b).hom =
      eqToHom b.property.symm := by
  dsimp only
  exact Functor.fiberToStructuredArrow_obj_hom (⟨0⟩ : QuillenQ C) _

/-- At the original completed unit, every time of the actual carried path is the zero Q vertex. -/
theorem completedCoreToOriginalHomotopyFiber_unit_path_apply
    (t : TopCat.I.{max u v}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀
              ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) t =
      SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
        (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)) := by
  let p := ExtensionCategory.localizedTarget (C := C)
  let q : QuillenQ C := ⟨0⟩
  let a : SInverse (Core C) (Core C) :=
    (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))
  let b : FixedTargetExtension.localizedFiber (C := C) (0 : C) :=
    (FixedTargetExtension.localizedFiberFunctor (C := C) (0 : C)).obj
      ((FixedTargetExtension.zeroLocalizedFunctor (C := C)).obj a)
  let c : StructuredArrow q p :=
    (Functor.fiberToStructuredArrow (p := p) q).obj b
  have hArrow : c.hom = eqToHom b.property.symm :=
    completedCoreUnitLeftComma_hom_eqToHom (C := C)
  have hVertex := completedCoreToZeroLeftCommaNerveMap_vertex (C := C) a
  change SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))
      (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
        (ComposableArrows.mk₀ a)) =
    SSet.realizedVertex
      (X := (nerve (StructuredArrow q p) : SSet.{max u v}))
      (ComposableArrows.mk₀ c) at hVertex
  have hFixed :=
    SSet.leftCommaHomotopyFiberComparison_vertex_path_const_of_hom_eqToHom.{
      u, 0, max u v} p q c b.property.symm hArrow t
  have hImage := congrArg
    (fun z : SSet.toTop.obj (nerve (StructuredArrow q p) : SSet.{max u v}) =>
      TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0} p))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ q))
        (SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v} p q z) t) hVertex
  change TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0} p))
      (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
        (ComposableArrows.mk₀ q))
      (SSet.leftCommaHomotopyFiberComparison.{u, 0, max u v} p q
        (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C))
          (SSet.realizedVertex
            (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a)))) t = _
  exact hImage.trans hFixed

/-- The original unit carries the literal constant compact-open path, with no path replacement. -/
theorem completedCoreToOriginalHomotopyFiber_unit_path_eq_const :
    TopCat.homotopyFiberPath
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀
              ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) =
      ContinuousMap.const TopCat.I.{max u v}
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))) := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.const_apply]
  exact completedCoreToOriginalHomotopyFiber_unit_path_apply (C := C) t

end AlgebraicKTheory.OriginalQZeroComparison

end
