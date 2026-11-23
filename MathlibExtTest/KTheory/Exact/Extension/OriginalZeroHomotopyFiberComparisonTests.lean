/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberComparison

/-!
# The original completed-Core comparison and all its coordinates

The clients retain arbitrary original Core pairs and denominators, the actual
localized target and Q zero vertex, and every carried compact-open path time.
The selected point is the positive inclusion of Core's unit, with both original
zero coordinates. Original base-family hypotheses derive weakness; the ring
client derives that family and uses the actual projective comparison theorem.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

namespace MathlibExtTest.OriginalQZeroComparison

open AlgebraicKTheory AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Every original pair and the canonical original unit retain their literal total vertices. -/
theorem original_all_pair_and_unit_total_coordinates (a : SInverse (Core C) (Core C)) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ a))) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)).obj a)) ∧
      ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))).toProd =
        ((⟨(0 : C)⟩ : Core C), (⟨(0 : C)⟩ : Core C)) ∧
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C)
          (SSet.realizedVertex (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
            (ComposableArrows.mk₀ ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))))) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C)).obj
            ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) := by
  exact ⟨completedCoreToOriginalHomotopyFiber_toTotal_vertex a,
    SInverse.inclusion_obj (Core C) (Core C) (𝟙_ (Core C)),
    completedCoreToOriginalHomotopyFiber_unit_toTotal (C := C)⟩

/-- The actual total and complete opposite path are observed together at arbitrary z and t. -/
theorem original_full_total_and_carried_path
    (z : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v}))
    (t : TopCat.I.{max u v}) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C) z) =
      SSet.toTop.map (nerveMapCommonHomUp.{u, max u v, 0}
        (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
          FixedTargetExtension.localizedForget (C := C) (0 : C))) z ∧
      TopCat.homotopyFiberPath
        (SSet.toTop.map
          (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (X := (nerve (QuillenQ C) : SSet.{max u v}))
          (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)))
        (completedCoreToOriginalHomotopyFiber (C := C) z) t =
      (SSet.nerveRealizationOppositeIso (QuillenQ C)).hom
        (TopCat.homotopyFiberPath
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C)).op))
          (SSet.realizedVertex (X := (nerve (QuillenQ C)ᵒᵖ : SSet.{max u v}))
            (ComposableArrows.mk₀ (op (⟨0⟩ : QuillenQ C))))
          (SSet.rightCommaHomotopyFiberComparison.{u, 0, max u v}
            (ExtensionCategory.localizedTarget (C := C)).op (op (⟨0⟩ : QuillenQ C))
            ((SSet.leftCommaRealizationIso.{u, 0, max u v}
              (ExtensionCategory.localizedTarget (C := C)) (op (⟨0⟩ : QuillenQ C))).hom
              (SSet.toTop.map (completedCoreToZeroLeftCommaNerveMap (C := C)) z))) t) := by
  exact ⟨ConcreteCategory.congr_hom
      (completedCoreToOriginalHomotopyFiber_toTotal (C := C)) z,
    completedCoreToOriginalHomotopyFiber_path_apply z t⟩

/-- Only the original base family derives weakness of the actual full comparison route. -/
theorem original_base_family_derives_full_comparison_weakness
    (hBase : ∀ X : C, TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj
        (nerve (MonoidalActionCategory (Core C) (FixedTargetExtension C X)) :
          SSet.{max u v})))) :
    TopCat.weakHomotopyEquivalences (completedCoreToOriginalHomotopyFiber (C := C)) ∧
      SSet.realizationWeakEquivalences (completedCoreToZeroLeftCommaNerveMap (C := C)) := by
  exact ⟨completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull hBase,
    completedCoreToZeroLeftCommaNerveMap_mem (C := C)⟩

/-- Every associative unital ring gives the actual comparison and original family at all objects. -/
theorem projective_actual_comparison_and_derived_original_bases
    {R : Type uRing} [Ring R] :
    TopCat.weakHomotopyEquivalences
        (completedCoreToOriginalHomotopyFiber (C := FGProjectiveCat.{vModule} R)) ∧
      (∀ X : FGProjectiveCat.{vModule} R, TopCat.weakHomotopyEquivalences
        (terminal.from (SSet.toTop.obj
          (nerve (MonoidalActionCategory (Core (FGProjectiveCat.{vModule} R))
            (FixedTargetExtension (FGProjectiveCat.{vModule} R) X)) :
              SSet.{max uRing (vModule + 1)})))) := by
  refine ⟨projectiveCompletedCoreToOriginalHomotopyFiber_mem (R := R), ?_⟩
  intro X
  exact AuxiliaryExtension.projectiveAuxiliary_realization_conull X

end MathlibExtTest.OriginalQZeroComparison

namespace AlgebraicKTheory.OriginalQZeroComparison

#print axioms completedCoreToZeroLeftCommaNerveMap
#print axioms completedCoreToZeroLeftCommaNerveMap_proj
#print axioms completedCoreToZeroLeftCommaNerveMap_mem
#print axioms completedCoreToOriginalHomotopyFiber
#print axioms completedCoreToOriginalHomotopyFiber_mem_of_originalBases_conull
#print axioms projectiveCompletedCoreToOriginalHomotopyFiber_mem
#print axioms completedCoreToOriginalHomotopyFiber_toTotal
#print axioms completedCoreToOriginalHomotopyFiber_toTotal_vertex
#print axioms completedCoreToOriginalHomotopyFiber_unit_toTotal
#print axioms completedCoreToOriginalHomotopyFiber_path_apply

end AlgebraicKTheory.OriginalQZeroComparison

namespace MathlibExtTest.OriginalQZeroComparison

#print axioms original_all_pair_and_unit_total_coordinates
#print axioms original_full_total_and_carried_path
#print axioms original_base_family_derives_full_comparison_weakness
#print axioms projective_actual_comparison_and_derived_original_bases

end MathlibExtTest.OriginalQZeroComparison

end
