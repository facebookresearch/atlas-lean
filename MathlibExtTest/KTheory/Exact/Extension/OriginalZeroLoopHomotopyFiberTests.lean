/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.OriginalZeroLoopHomotopyFiber

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory
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
#check AlgebraicKTheory.OriginalQZeroComparison.zeroFiberUnit
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroFiberUnit
#check AlgebraicKTheory.OriginalQZeroComparison.zeroFiberUnit_target
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroFiberUnit_target
#check AlgebraicKTheory.OriginalQZeroComparison.zeroTotalVertex
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroTotalVertex
#check AlgebraicKTheory.OriginalQZeroComparison.zeroQVertex
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroQVertex
#check AlgebraicKTheory.OriginalQZeroComparison.zeroTotalVertex_map
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroTotalVertex_map
#check AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber
#check AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_toTotal
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_toTotal
#check AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_path
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_path
#check AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_constant_point
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_constant_point
#check AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_mem
#print axioms AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_mem
#check AlgebraicKTheory.OriginalQZeroComparison.projectiveZeroLoopToOriginalHomotopyFiber_mem
#print axioms AlgebraicKTheory.OriginalQZeroComparison.projectiveZeroLoopToOriginalHomotopyFiber_mem


example :
    SSet.toTop.map
      (nerveMapCommonHom.{u, max u v, 0} (ExtensionCategory.localizedTarget (C := C)))
      (zeroTotalVertex (C := C)) = zeroQVertex (C := C) :=
  zeroTotalVertex_map (C := C)

example (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
    (zeroQVertex (C := C))) :
    TopCat.homotopyFiberToTotal
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
      (zeroLoopToOriginalHomotopyFiber (C := C) gamma) = zeroTotalVertex (C := C) :=
  ConcreteCategory.congr_hom (zeroLoopToOriginalHomotopyFiber_toTotal (C := C)) gamma

example (gamma : LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
    (zeroQVertex (C := C))) (t : TopCat.I.{max u v}) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
        (ExtensionCategory.localizedTarget (C := C)))) (zeroQVertex (C := C))
      (zeroLoopToOriginalHomotopyFiber (C := C) gamma) t =
        gamma ((TopCat.I.homeomorph.{max u v}) t) := by
  have h := ConcreteCategory.congr_hom (zeroLoopToOriginalHomotopyFiber_path (C := C)) gamma
  exact congrArg (fun f => f t) h

example :
    zeroLoopToOriginalHomotopyFiber (C := C) (Path.refl (zeroQVertex (C := C))) =
      TopCat.homotopyFiberSelectedPointMap
        (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (zeroTotalVertex (C := C)) (zeroQVertex (C := C))
        (zeroTotalVertex_map (C := C)) PUnit.unit :=
  ConcreteCategory.congr_hom (zeroLoopToOriginalHomotopyFiber_constant_point (C := C)) PUnit.unit

example : TopCat.weakHomotopyEquivalences (zeroLoopToOriginalHomotopyFiber (C := C)) :=
  zeroLoopToOriginalHomotopyFiber_mem (C := C)
end

example {R : Type uRing} [Ring R] :
    TopCat.weakHomotopyEquivalences
      (AlgebraicKTheory.OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber
        (C := FGProjectiveCat.{vModule} R)) :=
  AlgebraicKTheory.OriginalQZeroComparison.projectiveZeroLoopToOriginalHomotopyFiber_mem
    (R := R)
