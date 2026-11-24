/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import Batteries.Tactic.Lint
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Logic.Function.Basic

/-! # Full original variance clients: TypedFamilies

The complete original source bodies below retain their original contexts and checks.
-/

/-! Source body: GenericCompleteTypedValueJoin. -/
section OriginalFullSource024

set_option autoImplicit false
universe uA

namespace CategoryTheory.CompleteTypedValueJoin

/-- Join complete declared value families after their full types and ordinary value readbacks are fixed. -/
theorem heq {A : Sort uA} {B : Sort uA}
    (a₀ a₁ : A) (b₀ b₁ : B) (ha : a₀ = a₁) (hb : b₀ = b₁)
    (h : HEq a₁ b₁) : HEq a₀ b₀ := by
  cases ha
  cases hb
  exact h

end CategoryTheory.CompleteTypedValueJoin

end OriginalFullSource024

/-! Source body: GenericWholeDependentOperationCongruence. -/
section OriginalFullSource033

set_option autoImplicit false
universe u v
namespace CategoryTheory.WholeDependentOperationCongruence

/-- A whole argument identity is eliminated before a dependent operation reads endpoint or map fields. -/
theorem apply_heq {A : Sort u} (B : A → Sort v) (f : ∀ a, B a) (a b : A) (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

end CategoryTheory.WholeDependentOperationCongruence
end OriginalFullSource033

/-! Source body: GenericCompleteDependentFamilyOperator. -/
section OriginalFullSource034

set_option autoImplicit false
universe u v
namespace CategoryTheory.CompleteDependentFamilyOperator

/-- The full input/output function types are fixed before applying whole dependent operator and argument HEqs. -/
theorem apply_heq {A B : Sort u} (hA : A = B)
    (R0 : A → Sort v) (R1 : B → Sort v) (hR : HEq R0 R1)
    (F0 : ∀ a, R0 a) (F1 : ∀ b, R1 b) (hF : HEq F0 F1)
    (a : A) (b : B) (h : HEq a b) : HEq (F0 a) (F1 b) := by
  cases hA
  cases hR
  cases hF
  cases h
  rfl

end CategoryTheory.CompleteDependentFamilyOperator
end OriginalFullSource034

/-! Source body: GenericWholeComponentOperationFrame. -/
section OriginalFullSource035

set_option autoImplicit false
noncomputable section
universe uN vN uM vM uC vC uJ
open CategoryTheory
namespace CategoryTheory.WholeComponentOperationFrame

/-- Entire object, projection, inverse-functor and evaluation families precede the map operation. -/
def operator (N : Type uN) (cn : Category.{vN} N) (M : Type uM) (cm : Category.{vM} M)
    (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (F : @Functor N cn M cm) (X : M → J → C)
    (p : ∀ A B : M, @Quiver.Hom M cm.toCategoryStruct.toQuiver A B →
      ∀ a : J, @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a)) :=
  fun (A B : N) (f : @Quiver.Hom N cn.toCategoryStruct.toQuiver A B) (a : J) => p (F.obj A) (F.obj B) (F.map f) a

/-- All complete carrier, category, functor, object and projection identities are eliminated before native map endpoints. -/
theorem operator_heq (N : Type uN) (cn : Category.{vN} N)
    (M0 M1 : Type uM) (hM : M0 = M1)
    (m0 : Category.{vM} M0) (m1 : Category.{vM} M1) (hm : HEq m0 m1)
    (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (F0 : @Functor N cn M0 m0) (F1 : @Functor N cn M1 m1) (hF : HEq F0 F1)
    (X0 : M0 → J → C) (X1 : M1 → J → C) (hX : HEq X0 X1)
    (p0 : ∀ A B : M0, @Quiver.Hom M0 m0.toCategoryStruct.toQuiver A B →
      ∀ a : J, @Quiver.Hom C cc.toCategoryStruct.toQuiver (X0 A a) (X0 B a))
    (p1 : ∀ A B : M1, @Quiver.Hom M1 m1.toCategoryStruct.toQuiver A B →
      ∀ a : J, @Quiver.Hom C cc.toCategoryStruct.toQuiver (X1 A a) (X1 B a)) (hp : HEq p0 p1) :
    HEq (operator N cn M0 m0 C cc J F0 X0 p0) (operator N cn M1 m1 C cc J F1 X1 p1) := by
  cases hM
  cases hm
  cases hF
  cases hX
  cases hp
  rfl

end CategoryTheory.WholeComponentOperationFrame
end
end OriginalFullSource035

/-! Source body: GenericWholeFunctorEndpointMapApplication. -/
section OriginalFullSource036

set_option autoImplicit false
noncomputable section
universe uN vN uC vC uJ
open CategoryTheory
namespace CategoryTheory.WholeFunctorEndpointMapApplication

/-- Entire native functor endpoints and the value operation precede every full source arrow family. -/
def source (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G : N → @Functor N cn N cn) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows : ∀ Y Y' Z : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G Y).obj Z) ((G Y').obj Z)) :=
  fun Y Y' Z f a => operation ((G Y).obj Z) ((G Y').obj Z) (arrows Y Y' Z f) a

/-- Entire native functor endpoints and the value operation precede every full target arrow family. -/
def target (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G : N → @Functor N cn N cn) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows : ∀ Y Z Z' : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G Y).obj Z) ((G Y).obj Z')) :=
  fun Y Z Z' f a => operation ((G Y).obj Z) ((G Y).obj Z') (arrows Y Z Z' f) a

/-- Whole endpoint functor identity is consumed before source arrows or value map getters. -/
theorem source_heq (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G0 G1 : N → @Functor N cn N cn) (hG : G0 = G1) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows0 : ∀ Y Y' Z : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G0 Y).obj Z) ((G0 Y').obj Z))
    (arrows1 : ∀ Y Y' Z : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G1 Y).obj Z) ((G1 Y').obj Z)) (hArrow : HEq arrows0 arrows1) :
    HEq (source N cn C cc J G0 X operation arrows0) (source N cn C cc J G1 X operation arrows1) := by
  cases hG
  cases hArrow
  rfl

/-- Whole endpoint functor identity is consumed before target arrows or value map getters. -/
theorem target_heq (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G0 G1 : N → @Functor N cn N cn) (hG : G0 = G1) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows0 : ∀ Y Z Z' : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G0 Y).obj Z) ((G0 Y).obj Z'))
    (arrows1 : ∀ Y Z Z' : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G1 Y).obj Z) ((G1 Y).obj Z')) (hArrow : HEq arrows0 arrows1) :
    HEq (target N cn C cc J G0 X operation arrows0) (target N cn C cc J G1 X operation arrows1) := by
  cases hG
  cases hArrow
  rfl

end CategoryTheory.WholeFunctorEndpointMapApplication
end
end OriginalFullSource036

/-! Source body: GenericCarrierWholeFunctorEndpointMapApplication. -/
section OriginalFullSource037

set_option autoImplicit false
noncomputable section
universe uN vN uC vC uJ
open CategoryTheory
namespace CategoryTheory.CarrierWholeFunctorEndpointMapApplication

/-- Same full source application constructor after all carrier/category/functor types. -/
def source (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G : N → @Functor N cn N cn) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows : ∀ Y Y' Z : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G Y).obj Z) ((G Y').obj Z)) :=
  WholeFunctorEndpointMapApplication.source N cn C cc J G X operation arrows

/-- Same full target application constructor after all carrier/category/functor types. -/
def target (N : Type uN) (cn : Category.{vN} N) (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G : N → @Functor N cn N cn) (X : N → J → C)
    (operation : ∀ A B : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X A a) (X B a))
    (arrows : ∀ Y Z Z' : N, @Quiver.Hom N cn.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N cn.toCategoryStruct.toQuiver ((G Y).obj Z) ((G Y).obj Z')) :=
  WholeFunctorEndpointMapApplication.target N cn C cc J G X operation arrows

/-- Whole native carrier/category and result object types precede the complete source application values. -/
theorem source_heq (N0 N1 : Type uN) (hN : N0 = N1)
    (n0 : Category.{vN} N0) (n1 : Category.{vN} N1) (hn : HEq n0 n1)
    (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G0 : N0 → @Functor N0 n0 N0 n0) (G1 : N1 → @Functor N1 n1 N1 n1) (hG : HEq G0 G1)
    (X0 : N0 → J → C) (X1 : N1 → J → C) (hX : HEq X0 X1)
    (op0 : ∀ A B : N0, @Quiver.Hom N0 n0.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X0 A a) (X0 B a))
    (op1 : ∀ A B : N1, @Quiver.Hom N1 n1.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X1 A a) (X1 B a)) (hop : HEq op0 op1)
    (r0 : ∀ Y Y' Z : N0, @Quiver.Hom N0 n0.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N0 n0.toCategoryStruct.toQuiver ((G0 Y).obj Z) ((G0 Y').obj Z))
    (r1 : ∀ Y Y' Z : N1, @Quiver.Hom N1 n1.toCategoryStruct.toQuiver Y' Y →
      @Quiver.Hom N1 n1.toCategoryStruct.toQuiver ((G1 Y).obj Z) ((G1 Y').obj Z)) (hr : HEq r0 r1) :
    HEq (source N0 n0 C cc J G0 X0 op0 r0) (source N1 n1 C cc J G1 X1 op1 r1) := by
  cases hN
  cases hn
  cases hG
  cases hX
  cases hop
  cases hr
  rfl

/-- Whole native carrier/category and result object types precede the complete target application values. -/
theorem target_heq (N0 N1 : Type uN) (hN : N0 = N1)
    (n0 : Category.{vN} N0) (n1 : Category.{vN} N1) (hn : HEq n0 n1)
    (C : Type uC) (cc : Category.{vC} C) (J : Type uJ)
    (G0 : N0 → @Functor N0 n0 N0 n0) (G1 : N1 → @Functor N1 n1 N1 n1) (hG : HEq G0 G1)
    (X0 : N0 → J → C) (X1 : N1 → J → C) (hX : HEq X0 X1)
    (op0 : ∀ A B : N0, @Quiver.Hom N0 n0.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X0 A a) (X0 B a))
    (op1 : ∀ A B : N1, @Quiver.Hom N1 n1.toCategoryStruct.toQuiver A B → ∀ a : J,
      @Quiver.Hom C cc.toCategoryStruct.toQuiver (X1 A a) (X1 B a)) (hop : HEq op0 op1)
    (r0 : ∀ Y Z Z' : N0, @Quiver.Hom N0 n0.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N0 n0.toCategoryStruct.toQuiver ((G0 Y).obj Z) ((G0 Y).obj Z'))
    (r1 : ∀ Y Z Z' : N1, @Quiver.Hom N1 n1.toCategoryStruct.toQuiver Z Z' →
      @Quiver.Hom N1 n1.toCategoryStruct.toQuiver ((G1 Y).obj Z) ((G1 Y).obj Z')) (hr : HEq r0 r1) :
    HEq (target N0 n0 C cc J G0 X0 op0 r0) (target N1 n1 C cc J G1 X1 op1 r1) := by
  cases hN
  cases hn
  cases hG
  cases hX
  cases hop
  cases hr
  rfl

end CategoryTheory.CarrierWholeFunctorEndpointMapApplication
end
end OriginalFullSource037

/-! Source body: GenericCoherentNaturalitySquare. -/
section OriginalFullSource039

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory

namespace CategoryTheory.CoherentNaturalitySquare

/-- Keep every object and arrow of a naturality square before comparing its equation. -/
structure Frame (C : Type uC) [Category.{vC} C] where
  X : C
  X' : C
  Y : C
  Y' : C
  f : X ⟶ X'
  g : Y ⟶ Y'
  i : X ⟶ Y
  i' : X' ⟶ Y'

def Formula {C : Type uC} [Category.{vC} C] (d : Frame C) : Prop :=
  d.f ≫ d.i' = d.i ≫ d.g

/-- Transfer the equation only after the whole object and arrow frame is identified. -/
theorem of_frame_eq {C : Type uC} [Category.{vC} C]
    (d₀ d₁ : Frame C) (h : d₀ = d₁) (hd : Formula d₀) : Formula d₁ := by
  cases h
  exact hd

/-- Identify all four objects before the dependent actual arrows of the square. -/
theorem mk_eq {C : Type uC} [Category.{vC} C]
    (X₀ X₁ X'₀ X'₁ Y₀ Y₁ Y'₀ Y'₁ : C)
    (hX : X₀ = X₁) (hX' : X'₀ = X'₁) (hY : Y₀ = Y₁) (hY' : Y'₀ = Y'₁)
    (f₀ : X₀ ⟶ X'₀) (f₁ : X₁ ⟶ X'₁) (hf : HEq f₀ f₁)
    (g₀ : Y₀ ⟶ Y'₀) (g₁ : Y₁ ⟶ Y'₁) (hg : HEq g₀ g₁)
    (i₀ : X₀ ⟶ Y₀) (i₁ : X₁ ⟶ Y₁) (hi : HEq i₀ i₁)
    (i'₀ : X'₀ ⟶ Y'₀) (i'₁ : X'₁ ⟶ Y'₁) (hi' : HEq i'₀ i'₁) :
    (⟨X₀, X'₀, Y₀, Y'₀, f₀, g₀, i₀, i'₀⟩ : Frame C) =
      ⟨X₁, X'₁, Y₁, Y'₁, f₁, g₁, i₁, i'₁⟩ := by
  cases hX
  cases hX'
  cases hY
  cases hY'
  cases hf
  cases hg
  cases hi
  cases hi'
  rfl

end CategoryTheory.CoherentNaturalitySquare

end
end OriginalFullSource039

/-! Source body: GenericCompleteComposedFunctorMap. -/
section OriginalFullSource041

set_option autoImplicit false
noncomputable section
universe uA vA uB vB uC vC
open CategoryTheory

namespace CategoryTheory.CompleteComposedFunctorMap

/-- Complete categories and entire Functor values precede mapping one original source arrow through inverse/evaluation. -/
theorem heq (A : Type uA) (a₀ a₁ : Category.{vA} A) (ha : a₀ = a₁)
    (B : Type uB) (b₀ b₁ : Category.{vB} B) (hb : b₀ = b₁)
    (C : Type uC) (c : Category.{vC} C)
    (K₀ : @Functor A a₀ B b₀) (K₁ : @Functor A a₁ B b₁) (hK : HEq K₀ K₁)
    (F₀ : @Functor B b₀ C c) (F₁ : @Functor B b₁ C c) (hF : HEq F₀ F₁)
    (X₀ Y₀ X₁ Y₁ : A) (hX : X₀ = X₁) (hY : Y₀ = Y₁)
    (f₀ : @Quiver.Hom A a₀.toCategoryStruct.toQuiver X₀ Y₀)
    (f₁ : @Quiver.Hom A a₁.toCategoryStruct.toQuiver X₁ Y₁) (hf : HEq f₀ f₁) :
    HEq (@Functor.map B b₀ C c F₀
      (@Functor.obj A a₀ B b₀ K₀ X₀) (@Functor.obj A a₀ B b₀ K₀ Y₀)
      (@Functor.map A a₀ B b₀ K₀ X₀ Y₀ f₀))
      (@Functor.map B b₁ C c F₁
      (@Functor.obj A a₁ B b₁ K₁ X₁) (@Functor.obj A a₁ B b₁ K₁ Y₁)
      (@Functor.map A a₁ B b₁ K₁ X₁ Y₁ f₁)) := by
  cases ha
  cases hb
  cases hK
  cases hF
  cases hX
  cases hY
  cases hf
  exact HEq.rfl

end CategoryTheory.CompleteComposedFunctorMap

end
end OriginalFullSource041

/-! Source body: GenericCompleteFourValueJoin. -/
section OriginalFullSource042

set_option autoImplicit false
universe u

namespace CategoryTheory.CompleteTypedValueJoin

/-- Join coherent complete value families through named types before native HEq transitivity. -/
theorem four (A B C D : Sort u) (a : A) (b : B) (c : C) (d : D)
    (hab : HEq a b) (hbc : HEq b c) (hcd : HEq c d) : HEq a d :=
  hab.trans (hbc.trans hcd)

end CategoryTheory.CompleteTypedValueJoin

end OriginalFullSource042

/-! Source body: GenericCompleteFiveValueJoin. -/
section OriginalFullSource043

set_option autoImplicit false
universe u

namespace CategoryTheory.CompleteTypedValueJoin

/-- Compose five entire typed families only after all output types and complete value identities are supplied. -/
theorem five (A B C D E : Sort u) (a : A) (b : B) (c : C) (d : D) (e : E)
    (hab : HEq a b) (hbc : HEq b c) (hcd : HEq c d) (hde : HEq d e) : HEq a e :=
  hab.trans (hbc.trans (hcd.trans hde))

end CategoryTheory.CompleteTypedValueJoin

end OriginalFullSource043

/-! Source body: GenericCompleteValueObjectOperator. -/
section OriginalFullSource051

set_option autoImplicit false
noncomputable section
universe uN uJ uA vA uB vB
open CategoryTheory

namespace CategoryTheory.CompleteValueObjectOperator

/-- Complete original module-object type family precedes the whole evaluated value/Hom-input family. -/
def family {N : Type uN} {J : Type uJ} {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (X : N → N → A) (F : J → (A ⥤ B)) := fun n z a => (F a).obj (X n z)

/-- Whole module object family identity is consumed before original value/Hom-input output types. -/
theorem family_eq {N : Type uN} {J : Type uJ} {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (X₀ X₁ : N → N → A) (hX : X₀ = X₁) (F : J → (A ⥤ B)) : family X₀ F = family X₁ F :=
  congrArg (fun X => family X F) hX

end CategoryTheory.CompleteValueObjectOperator

end
end OriginalFullSource051

/-! Source body: GenericEvaluationMapOperationTypes. -/
section OriginalFullSource053

set_option autoImplicit false
noncomputable section
universe uJ uA vA uB vB
open CategoryTheory

namespace CategoryTheory.EvaluationMapOperationTypes

/-- Complete evaluation map function type, before source module objects or arrows. -/
def Types {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (J : Type uJ) (F : J → (A ⥤ B)) :=
  ∀ M N : A, (M ⟶ N) → ∀ a : J, (F a).obj M ⟶ (F a).obj N

/-- Whole evaluationFunctor identity precedes its complete map operation output function types. -/
theorem types_eq {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (J : Type uJ) (F₀ F₁ : J → (A ⥤ B)) (hF : F₀ = F₁) : Types J F₀ = Types J F₁ :=
  congrArg (Types J) hF

end CategoryTheory.EvaluationMapOperationTypes

end
end OriginalFullSource053

/-! Source body: GenericExactNaturalityEquationTransport. -/
section OriginalFullSource054

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory

namespace CategoryTheory.ExactNaturalityEquationTransport

/-- Identify all exact native endpoints before transferring their actual composition equation. -/
theorem equation {C : Type uC} [Category.{vC} C]
    (X₀ X₁ X'₀ X'₁ Y₀ Y₁ Y'₀ Y'₁ : C)
    (hX : X₀ = X₁) (hX' : X'₀ = X'₁) (hY : Y₀ = Y₁) (hY' : Y'₀ = Y'₁)
    (f₀ : X₀ ⟶ X'₀) (f₁ : X₁ ⟶ X'₁) (hf : HEq f₀ f₁)
    (g₀ : Y₀ ⟶ Y'₀) (g₁ : Y₁ ⟶ Y'₁) (hg : HEq g₀ g₁)
    (i₀ : X₀ ⟶ Y₀) (i₁ : X₁ ⟶ Y₁) (hi : HEq i₀ i₁)
    (i'₀ : X'₀ ⟶ Y'₀) (i'₁ : X'₁ ⟶ Y'₁) (hi' : HEq i'₀ i'₁)
    (h : f₀ ≫ i'₀ = i₀ ≫ g₀) : f₁ ≫ i'₁ = i₁ ≫ g₁ := by
  cases hX
  cases hX'
  cases hY
  cases hY'
  cases hf
  cases hg
  cases hi
  cases hi'
  exact h

end CategoryTheory.ExactNaturalityEquationTransport

end
end OriginalFullSource054

/-! Source body: GenericModuleMapOperationReindex. -/
section OriginalFullSource067

set_option autoImplicit false
noncomputable section
universe uI vI uA vA uB vB uJ
open CategoryTheory

namespace CategoryTheory.ModuleMapOperationReindex

/-- Reindex complete module evaluation map operations after all endpoint type families, operation types and values are identified. -/
theorem heq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (J : Type uJ) (F₀ F₁ : J → (A ⥤ B)) (hF : F₀ = F₁)
    (op₀ : EvaluationMapOperationTypes.Types J F₀) (op₁ : EvaluationMapOperationTypes.Types J F₁) (hop : HEq op₀ op₁)
    (X X' : I → I → A)
    (maps : ∀ Y Y' Z, (Y' ⟶ Y) → (X Y Z ⟶ X' Y' Z)) :
    HEq (fun Y Y' Z f a => op₀ (X Y Z) (X' Y' Z) (maps Y Y' Z f) a)
      (fun Y Y' Z f a => op₁ (X Y Z) (X' Y' Z) (maps Y Y' Z f) a) := by
  cases hF
  cases hop
  exact HEq.rfl

end CategoryTheory.ModuleMapOperationReindex

end
end OriginalFullSource067

/-! Source body: GenericProofInputFamilyCongruence. -/
section OriginalFullSource074

set_option autoImplicit false
noncomputable section
universe uR

namespace CategoryTheory.ProofInputFamilyCongruence

/-- Identify complete proof-input propositions before comparing any constructed output family. -/
theorem two {P Q : Prop} {R : Sort uR} (F : P → Q → R)
    (p₀ p₁ : P) (q₀ q₁ : Q) : F p₀ q₀ = F p₁ q₁ := by
  have hp : p₀ = p₁ := Subsingleton.elim _ _
  have hq : q₀ = q₁ := Subsingleton.elim _ _
  cases hp
  cases hq
  rfl

end CategoryTheory.ProofInputFamilyCongruence

end
end OriginalFullSource074

/-! Source body: GenericTypedFamilyValueApply. -/
section OriginalFullSource076

set_option autoImplicit false
universe uI uR

namespace CategoryTheory.TypedFamilyValueApply

/-- Apply a whole typed family only after complete dependent output types and value identity. -/
theorem heq {I : Type uI} (B₀ B₁ : I → Sort uR) (hB : B₀ = B₁)
    (f₀ : ∀ i, B₀ i) (f₁ : ∀ i, B₁ i) (hf : HEq f₀ f₁) (i : I) : HEq (f₀ i) (f₁ i) := by
  cases hB
  cases hf
  exact HEq.rfl

end CategoryTheory.TypedFamilyValueApply

end OriginalFullSource076

/-! Source body: GenericWholeSourceMapFamilyApply. -/
section OriginalFullSource082

set_option autoImplicit false
universe uI vI uJ uR
open CategoryTheory

namespace CategoryTheory.WholeSourceMapFamilyApply

/-- Apply an entire source map family only after its complete output types are identified. -/
theorem heq {I : Type uI} [Category.{vI} I] {J : Type uJ}
    (R₀ R₁ : ∀ Y Y' _Z : I, (Y' ⟶ Y) → J → Sort uR) (hR : R₀ = R₁)
    (f₀ : ∀ Y Y' Z g a, R₀ Y Y' Z g a) (f₁ : ∀ Y Y' Z g a, R₁ Y Y' Z g a) (hf : HEq f₀ f₁)
    (Y Y' Z : I) (g : Y' ⟶ Y) (a : J) : HEq (f₀ Y Y' Z g a) (f₁ Y Y' Z g a) := by
  cases hR
  cases hf
  exact HEq.rfl

end CategoryTheory.WholeSourceMapFamilyApply

end OriginalFullSource082

/-! Source body: GenericWholeSourceMapOutputTypes. -/
section OriginalFullSource083

set_option autoImplicit false
noncomputable section
universe uN vN uJ uC vC
open CategoryTheory

namespace CategoryTheory.WholeSourceMapOutputTypes

/-- Complete source map output arrow type family before source/target/parameter getters. -/
def Types {N : Type uN} [Category.{vN} N] {J : Type uJ} {C : Type uC} [Category.{vC} C]
    (X : N → N → J → C) :=
  fun Y Y' Z : N => fun (_f : Y' ⟶ Y) (a : J) => X Y Z a ⟶ X Y' Z a

/-- Entire value object family equality precedes the full source map output type family. -/
theorem types_eq {N : Type uN} [Category.{vN} N] {J : Type uJ} {C : Type uC} [Category.{vC} C]
    (X₀ X₁ : N → N → J → C) (hX : X₀ = X₁) : Types X₀ = Types X₁ := congrArg Types hX

end CategoryTheory.WholeSourceMapOutputTypes

end
end OriginalFullSource083
