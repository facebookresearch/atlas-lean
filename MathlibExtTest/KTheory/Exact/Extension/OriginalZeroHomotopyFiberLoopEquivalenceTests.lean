/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopEquivalence
import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopPointPairEquivalence

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open AlgebraicKTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory ZeroObject Simplicial

universe u v uRing vModule

section
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

open AlgebraicKTheory.OriginalQZeroComparison
#check AlgebraicKTheory.OriginalQZeroComparison.originalLocalizedTotalTerminalWeak
#print axioms AlgebraicKTheory.OriginalQZeroComparison.originalLocalizedTotalTerminalWeak
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_invFun
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_invFun
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_mem
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_mem
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_selectedPoint
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_selectedPoint
#check AlgebraicKTheory.OriginalQZeroComparison.projectiveOriginalHomotopyFiberLoopEquiv
#print axioms AlgebraicKTheory.OriginalQZeroComparison.projectiveOriginalHomotopyFiberLoopEquiv
#check AlgebraicKTheory.OriginalQZeroComparison.projectiveOriginalHomotopyFiberToLoops_mem
#print axioms AlgebraicKTheory.OriginalQZeroComparison.projectiveOriginalHomotopyFiberToLoops_mem


#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_toFun
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_toFun
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_eq_realizedConull
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_eq_realizedConull

example : (zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun =
    (zeroOriginalHomotopyFiberToLoops (C := C)).hom :=
  zeroOriginalHomotopyFiberLoopEquiv_toFun (C := C)

example : (zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun =
    (zeroLoopToOriginalHomotopyFiber (C := C)).hom :=
  zeroOriginalHomotopyFiberLoopEquiv_invFun (C := C)

example : Nonempty (ContinuousMap.Homotopy
    ((zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun.comp
      (zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun)
    (ContinuousMap.id (TopCat.homotopyFiber
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))))) :=
  (zeroOriginalHomotopyFiberLoopEquiv (C := C)).left_inv

example : Nonempty (ContinuousMap.Homotopy
    ((zeroOriginalHomotopyFiberLoopEquiv (C := C)).toFun.comp
      (zeroOriginalHomotopyFiberLoopEquiv (C := C)).invFun)
    (ContinuousMap.id (LoopSpace
      (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v})) (zeroQVertex (C := C))))) :=
  (zeroOriginalHomotopyFiberLoopEquiv (C := C)).right_inv

example :
    zeroOriginalHomotopyFiberToLoops (C := C)
      (TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
        (zeroTotalVertex_map (C := C)) PUnit.unit) = Path.refl (zeroQVertex (C := C)) :=
  ConcreteCategory.congr_hom
    (zeroOriginalHomotopyFiberToLoops_selectedPoint (C := C)) PUnit.unit

end

#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv_hom_fst
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv_hom_fst
#check AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv_inv_fst
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv_inv_fst

section
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

open AlgebraicKTheory.OriginalQZeroComparison

example (s : unitInterval) :
    zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := C)
        (s, TopCat.homotopyFiberSelectedPointMap
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C))))
          (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
          (zeroTotalVertex_map (C := C)) PUnit.unit) =
      TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
        (zeroTotalVertex_map (C := C)) PUnit.unit :=
  (zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := C)).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (s : unitInterval) :
    zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := C)
      (s, Path.refl (zeroQVertex (C := C))) = Path.refl (zeroQVertex (C := C)) :=
  (zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := C)).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)

example (s : unitInterval) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
      (zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := C)
        (s, TopCat.homotopyFiberSelectedPointMap
          (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
            (ExtensionCategory.localizedTarget (C := C))))
          (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
          (zeroTotalVertex_map (C := C)) PUnit.unit)) =
      ContinuousMap.const TopCat.I.{max u v} (zeroQVertex (C := C)) := by
  have fixed := (zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := C)).eq_snd
    s (Set.mem_singleton_iff.mpr rfl)
  exact (congrArg (TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))) fixed).trans
    (ConcreteCategory.congr_hom (TopCat.homotopyFiberSelectedPointMap_path
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
      (zeroTotalVertex_map (C := C))) PUnit.unit)

example (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
    (zeroQVertex (C := C))) :
    zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := C) (1, gamma) = gamma :=
  (zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := C)).toHomotopy.apply_one gamma

example :
    (TopPair.Hom.fst (zeroOriginalHomotopyFiberLoopPointPairEquiv (C := C)).hom).hom =
      (zeroOriginalHomotopyFiberToLoops (C := C)).hom := by
  exact congrArg TopCat.Hom.hom
    (zeroOriginalHomotopyFiberLoopPointPairEquiv_hom_fst (C := C))

example :
    (TopPair.Hom.fst (zeroOriginalHomotopyFiberLoopPointPairEquiv (C := C)).inv).hom =
      (zeroLoopToOriginalHomotopyFiber (C := C)).hom := by
  exact congrArg TopCat.Hom.hom
    (zeroOriginalHomotopyFiberLoopPointPairEquiv_inv_fst (C := C))
end

example {R : Type uRing} [Ring R] :
    (TopPair.Hom.fst
      (AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv
        (C := FGProjectiveCat.{vModule} R)).inv).hom =
      (AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber
        (C := FGProjectiveCat.{vModule} R)).hom := by
  exact congrArg TopCat.Hom.hom
    (AlgebraicKTheory.OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopPointPairEquiv_inv_fst
      (C := FGProjectiveCat.{vModule} R))
