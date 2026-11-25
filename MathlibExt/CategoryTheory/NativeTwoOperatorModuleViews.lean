/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeOppositeBimoduleModels

/-!
# Full commuting-operator views of native modules

The two embeddings have their original commuting multiplication square.
The carrier and every map are the original module. Both actions are fixed
by those embeddings, the original action and actual opposite-ring carrier.
This retains full X and P actions when forming product tau-Hom or balanced
P-tensor. It does not select a new coefficient object.

Source: DK1311.2374v2 Sections4.10,8.2; Mathlib56a005 native Mon/Bimod,
Apache2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeTwoOperatorModuleViews

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open NativeOppositeBimoduleModels

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (D K R S Sop : Mon C) (leftEmbedding : R ⟶ D) (secondEmbedding : S ⟶ D)
  (opposite : OppositeMonoidSource S Sop)

def CommutingEmbeddings : Prop :=
  (leftEmbedding.hom ⊗ₘ secondEmbedding.hom) ≫ μ[D.X] =
    (β_ R.X S.X).hom ≫ (secondEmbedding.hom ⊗ₘ leftEmbedding.hom) ≫ μ[D.X]

/-- The full commuting actions are computed from the original native operator embeddings. -/
structure TwoOperatorViewSource where
  functor : Bimod D K ⥤ Bimod R Sop
  underlying : functor ⋙ Bimod.forget (B := Sop) R ≅ Bimod.forget (B := K) D
  leftAction : ∀ F : Bimod D K,
    (functor.obj F).actLeft ≫ underlying.hom.app F =
      (leftEmbedding.hom ⊗ₘ underlying.hom.app F) ≫ F.actLeft
  rightAction : ∀ F : Bimod D K,
    (functor.obj F).actRight ≫ underlying.hom.app F =
      (underlying.hom.app F ⊗ₘ opposite.carrier.hom) ≫ (β_ F.X S.X).hom ≫
        (secondEmbedding.hom ⊗ₘ 𝟙 F.X) ≫ F.actLeft

end MathlibExt.CategoryTheory.NativeTwoOperatorModuleViews
