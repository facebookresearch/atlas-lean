/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import MathlibExt.CategoryTheory.NativeParametrizedAdjoints

/-!
# Actual balanced bimodule tensor and its module Hom

Tensor is Mathlib's coequalizer of the two original middle-ring actions.
Both outer actions and every parameter map are retained. Module Hom is
the native right adjoint of that same balanced tensor. This supports
tempered/exponential modules while retaining the commuting X action.

Source: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
CategoryTheory/Monoidal/Bimod (Kim Morrison, Oleksandr Manzyuk), Apache 2.0;
DK arXiv:1311.2374v2, Sections 5.2, 8.2 and 9.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeBimoduleTensorOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open NativeParametrizedAdjoints

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (R S T : Mon C)

/-- Balance the actual middle S-action and preserve both outer actions. -/
def tensorLeftModule (M : Bimod R S) : Bimod S T ⥤ Bimod R T where
  obj N := M.tensorBimod N
  map f := Bimod.whiskerLeft M f
  map_id _N := Bimod.whiskerLeft_id_bimod
  map_comp f g := Bimod.whiskerLeft_comp_bimod M f g

/-- The same actual balanced tensor with the right operand fixed. -/
def tensorRightModule (N : Bimod S T) : Bimod R S ⥤ Bimod R T where
  obj M := M.tensorBimod N
  map f := Bimod.whiskerRight f N
  map_id _M := Bimod.id_whiskerRight_bimod
  map_comp f g := Bimod.comp_whiskerRight_bimod f g N

/-- The complete bifunctor, with its original bimodule action maps. -/
def tensorModules : Bimod R S ⥤ Bimod S T ⥤ Bimod R T where
  obj M := tensorLeftModule R S T M
  map f :=
    { app N := Bimod.whiskerRight f N
      naturality N N' g := Bimod.whisker_exchange_bimod f g }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact Bimod.id_whiskerRight_bimod (M := M) (N := N)
  map_comp f g := by
    apply NatTrans.ext
    funext N
    exact Bimod.comp_whiskerRight_bimod f g N

/-- The source ordering used for Hom over the original right ring. -/
def tensorModulesFlipped : Bimod S T ⥤ Bimod R S ⥤ Bimod R T where
  obj N := tensorRightModule R S T N
  map f :=
    { app M := Bimod.whiskerLeft M f
      naturality M M' g := (Bimod.whisker_exchange_bimod g f).symm }
  map_id N := by
    apply NatTrans.ext
    funext M
    exact Bimod.whiskerLeft_id_bimod (M := M) (N := N)
  map_comp f g := by
    apply NatTrans.ext
    funext M
    exact Bimod.whiskerLeft_comp_bimod M f g

/-- Structural closedness of the prescribed balanced coefficient tensor. -/
structure ModuleHomSource : Prop where
  closed : ∀ N : Bimod S T, ((tensorModulesFlipped R S T).obj N).IsLeftAdjoint

/-- Native module Hom retains R and reverses its source S--T module. -/
def moduleHom (H : ModuleHomSource R S T) :
    (Bimod S T)ᵒᵖ ⥤ Bimod R T ⥤ Bimod R S :=
  letI := H.closed
  rightAdjointBifunctor (tensorModulesFlipped R S T)

/-- Evaluation is the actual counit of the original balanced tensor. -/
def moduleEvaluation (H : ModuleHomSource R S T) (N : Bimod S T) (L : Bimod R T) :
    ((tensorModulesFlipped R S T).obj N).obj
      (((moduleHom R S T H).obj (op N)).obj L) ⟶ L :=
  letI := H.closed
  (Adjunction.ofIsLeftAdjoint ((tensorModulesFlipped R S T).obj N)).counit.app L

end MathlibExt.CategoryTheory.NativeBimoduleTensorOperators
