/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation

/-!
# Bousfield--Kan augmentation tests

These tests pin the generic terminal-weight bar augmentation, its diagonal
Bousfield--Kan augmentation, the weighted-summand computation, and naturality.
They make no simplex-resolution, contraction, weak-equivalence, realization,
or Theorem A claim.
-/

open CategoryTheory Opposite Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentationTests

universe u

variable {J : Type u} [Category.{0} J]
variable {D E : J ⥤ SSet.{u}} {A B : SSet.{u}}

/-- Generic cocones induce terminal-weight bar and BK augmentations. -/
noncomputable example (τ : D ⟶ (Functor.const J).obj A) :
    StrictOrdinaryWeightedBar.wbarSimplicial
        (CategoryBar.replUnit J) D ⟶
      (SimplicialObject.const SSet.{u}).obj A :=
  SSet.wbarAugmentation τ

noncomputable example (τ : D ⟶ (Functor.const J).obj A) :
    SSet.bkHocolim D ⟶ A :=
  SSet.bkAugmentation τ

/-- The BK augmentation restricts to the cocone map on every weighted
summand. -/
example (τ : D ⟶ (Functor.const J).obj A) (n : ℕ)
    (s : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n s).app (op ⦋n⦌) ≫
      (SSet.bkAugmentation τ).app (op ⦋n⦌) =
        (τ.app s.1.left).app (op ⦋n⦌) :=
  SSet.bkAugmentation_app_mk_ι τ n s

/-- BK augmentations are natural for maps of cocones. -/
example (α : D ⟶ E)
    (τ : D ⟶ (Functor.const J).obj A)
    (τ' : E ⟶ (Functor.const J).obj B) (u : A ⟶ B)
    (h : ∀ j, α.app j ≫ τ'.app j = τ.app j ≫ u) :
    SSet.bkHocolimMap α ≫ SSet.bkAugmentation τ' =
      SSet.bkAugmentation τ ≫ u :=
  SSet.bkAugmentation_naturality α τ τ' u h

/-- Identity maps of cocones specialize augmentation naturality strictly. -/
example (τ : D ⟶ (Functor.const J).obj A) :
    SSet.bkHocolimMap (𝟙 D) ≫ SSet.bkAugmentation τ =
      SSet.bkAugmentation τ ≫ 𝟙 A :=
  SSet.bkAugmentation_naturality (𝟙 D) τ τ (𝟙 A) (fun _ => by simp)

/-- Outer degrees zero and one both retain the literal left endpoint. -/
example (τ : D ⟶ (Functor.const J).obj A)
    (s₀ : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) 0)
    (s₁ : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) 1) :
    (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D 0 s₀).app (op ⦋0⦌) ≫
        (SSet.bkAugmentation τ).app (op ⦋0⦌) =
          (τ.app s₀.1.left).app (op ⦋0⦌) ∧
      (StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D 1 s₁).app (op ⦋1⦌) ≫
        (SSet.bkAugmentation τ).app (op ⦋1⦌) =
          (τ.app s₁.1.left).app (op ⦋1⦌) :=
  ⟨SSet.bkAugmentation_app_mk_ι τ 0 s₀,
    SSet.bkAugmentation_app_mk_ι τ 1 s₁⟩

section UniverseOne

variable {J₁ : Type 1} [Category.{0} J₁]
variable {D₁ : J₁ ⥤ SSet.{1}} {A₁ : SSet.{1}}

noncomputable example (τ : D₁ ⟶ (Functor.const J₁).obj A₁) :
    SSet.bkHocolim D₁ ⟶ A₁ :=
  SSet.bkAugmentation τ

end UniverseOne

section UniverseZero

variable {J₀ : Type} [Category J₀]
variable {D₀ : J₀ ⥤ SSet.{0}} {A₀ : SSet.{0}}

noncomputable example (τ : D₀ ⟶ (Functor.const J₀).obj A₀) :
    SSet.bkHocolim D₀ ⟶ A₀ :=
  SSet.bkAugmentation τ

noncomputable example :
    let J := Discrete Empty
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.bkHocolim D ⟶ (⊥_ SSet.{0}) :=
  SSet.bkAugmentation (𝟙 _)

noncomputable example :
    let J := Discrete Bool
    let D := (Functor.const J).obj (⊥_ SSet.{0})
    SSet.bkHocolim D ⟶ (⊥_ SSet.{0}) :=
  SSet.bkAugmentation (𝟙 _)

end UniverseZero

section GeneralizedTargetMixed

variable {Jm : Type} [Category.{0} Jm]
variable {Dm Em : Jm ⥤ SSet.{1}} {Am Bm : SSet.{1}}

/-- Generalized-target augmentation elaborates with an explicit target
level. -/
noncomputable example (τ : Dm ⟶ (Functor.const Jm).obj Am) :
    SSet.bkHocolimOf.{0, 0, 1} Dm ⟶ Am :=
  SSet.bkAugmentationOf.{0, 0, 1} τ

/-- Summand restriction at the generalized target. -/
example (τ : Dm ⟶ (Functor.const Jm).obj Am) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx Jm (CategoryBar.replUnit Jm) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Jm) Dm n p).app (op ⦋n⦌) ≫
      (SSet.bkAugmentationOf.{0, 0, 1} τ).app (op ⦋n⦌) =
        (τ.app p.1.left).app (op ⦋n⦌) :=
  SSet.bkAugmentationOf_app_mk_ι.{0, 0, 1} τ n p

/-- Augmentation naturality at the generalized target. -/
example (α : Dm ⟶ Em)
    (τ : Dm ⟶ (Functor.const Jm).obj Am)
    (τ' : Em ⟶ (Functor.const Jm).obj Bm) (u : Am ⟶ Bm)
    (h : ∀ j, α.app j ≫ τ'.app j = τ.app j ≫ u) :
    SSet.bkHocolimMapOf.{0, 0, 1} α ≫
        SSet.bkAugmentationOf.{0, 0, 1} τ' =
      SSet.bkAugmentationOf.{0, 0, 1} τ ≫ u :=
  SSet.bkAugmentationOf_naturality.{0, 0, 1} α τ τ' u h

end GeneralizedTargetMixed

#print axioms SSet.wbarAugmentationZero_isBalanced
#print axioms SSet.bkAugmentation_app_mk_ι
#print axioms SSet.bkAugmentation_naturality
#print axioms SSet.bkAugmentationOf_app_mk_ι
#print axioms SSet.bkAugmentationOf_naturality

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentationTests
