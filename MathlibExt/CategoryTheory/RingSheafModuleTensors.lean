/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Native tensor and exterior powers of ring-module sheaves

Tensor products are the native sectionwise tensor presheaf followed by
the native module sheafification. The generator uses that same original
sheafification unit. Exterior powers similarly use the completed
semilinear presheaf construction and module sheafification.

Native source: Mathlib ModuleCat/Presheaf/Monoidal.lean and
ModuleCat/Presheaf/Sheafification.lean, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.RingSheafModuleTensors

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open RingedDerivedCoefficientOperations
open scoped TensorProduct

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (S : Sheaf J CommRingCat.{1})

def moduleSheafification :=
  PresheafOfModules.sheafification (R := moduleRing S) (𝟙 (moduleRing S).obj)

def tensorFunctor (N : Modules S) : Modules S ⥤ Modules S :=
  SheafOfModules.forget (moduleRing S) ⋙
    (tensoringRight (PresheafOfModulesOfCommRing.{1} S.obj)).obj N.val ⋙
      moduleSheafification S

abbrev tensor (M N : Modules S) : Modules S := (tensorFunctor S N).obj M

def generator (M N : Modules S) (U : Cᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensor S M N).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction (R := moduleRing S)
      (𝟙 (moduleRing S).obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := S.obj) M.val N.val)).app U).hom
    (m ⊗ₜ[S.obj.obj U] n)

def exterior (M : Modules S) (n : ℕ) : Modules S :=
  (moduleSheafification S).obj (PresheafOfModules.extPow.{v, u, 1, 0} (O := S.obj) n M.val)

end MathlibExt.CategoryTheory.RingSheafModuleTensors
