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

/-! # Full original variance clients: FunctorFamilies

The complete original source bodies below retain their original contexts and checks.
-/

/-! Source body: GenericFunctorObjectMapReadbacks. -/
section OriginalFullSource004

set_option autoImplicit false
noncomputable section
universe uA vA uB vB
open CategoryTheory

namespace CategoryTheory.FunctorObjectMapReadbacks

/-- Identify the complete target functors before any object getter. -/
theorem obj_eq {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F G : A ⥤ B) (h : F = G) (X : A) : F.obj X = G.obj X := congrArg (fun F => F.obj X) h

/-- Identify the complete target functors before any dependent map getter. -/
theorem map_heq {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F G : A ⥤ B) (h : F = G) {X Y : A} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  rfl

end CategoryTheory.FunctorObjectMapReadbacks

end
end OriginalFullSource004

/-! Source body: GenericNatTransAppTransport. -/
section OriginalFullSource005

set_option autoImplicit false
noncomputable section
universe uA vA uB vB
open CategoryTheory

namespace CategoryTheory.NatTransAppTransport

/-- Identify complete source/target functors and the whole transformation before a scalar component is read. -/
theorem app_heq {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F₀ F₁ G₀ G₁ : A ⥤ B) (hF : F₀ = F₁) (hG : G₀ = G₁)
    (s₀ : F₀ ⟶ G₀) (s₁ : F₁ ⟶ G₁) (hs : HEq s₀ s₁) (X : A) :
    HEq (s₀.app X) (s₁.app X) := by
  cases hF
  cases hG
  cases hs
  rfl

end CategoryTheory.NatTransAppTransport

end
end OriginalFullSource005

/-! Source body: GenericInverseFunctorIsoNaturality. -/
section OriginalFullSource007

set_option autoImplicit false
noncomputable section
universe uA vA uB vB
open CategoryTheory

namespace CategoryTheory.InverseFunctorIsoNaturality

/-- Map an entire inverse Iso naturality square after its four actual arrows and objects are typed. -/
theorem map_square {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F : A ⥤ B) {X₀ X₁ Y₀ Y₁ : A} (f : X₀ ⟶ X₁) (g : Y₀ ⟶ Y₁)
    (i₀ : Y₀ ≅ X₀) (i₁ : Y₁ ≅ X₁) (h : f ≫ i₁.inv = i₀.inv ≫ g) :
    F.map f ≫ (F.mapIso i₁).inv = (F.mapIso i₀).inv ≫ F.map g := by
  change F.map f ≫ F.map i₁.inv = F.map i₀.inv ≫ F.map g
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map h

end CategoryTheory.InverseFunctorIsoNaturality

end
end OriginalFullSource007

/-! Source body: GenericSourceIsoFamilyOfFunctorIsos. -/
section OriginalFullSource013

set_option autoImplicit false
noncomputable section
universe uI uA vA uB vB
open CategoryTheory

namespace CategoryTheory.SourceIsoFamilyOfFunctorIsos

/-- Retain the complete original inverse mapIso source family after both whole target functor families. -/
def family {I : Type uI} {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F G : I → (A ⥤ A)) (i : ∀ X, F X ≅ G X) (K : A ⥤ B) :=
  fun X : I => fun Y : A => (K.mapIso ((i X).app Y)).symm

/-- Whole functor-Iso family value equality precedes every original inverse mapIso component. -/
theorem family_eq {I : Type uI} {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F G : I → (A ⥤ A)) (i₀ i₁ : ∀ X, F X ≅ G X) (hi : i₀ = i₁) (K : A ⥤ B) :
    family F G i₀ K = family F G i₁ K := congrArg (fun i => family F G i K) hi

end CategoryTheory.SourceIsoFamilyOfFunctorIsos

end
end OriginalFullSource013

/-! Source body: GenericNatIsoSourceRetarget. -/
section OriginalFullSource014

set_option autoImplicit false
noncomputable section
universe uA vA uB vB
open CategoryTheory

namespace CategoryTheory.NatIsoSourceRetarget

/-- Retarget the entire NatIso source functor before any native component is read. -/
def transport {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F₀ F₁ G : A ⥤ B) (h : F₀ = F₁) (i : F₁ ≅ G) : F₀ ≅ G :=
  h.symm ▸ i

/-- The complete actual comparison value is unchanged after whole source-functor identity. -/
theorem transport_heq {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (F₀ F₁ G : A ⥤ B) (h : F₀ = F₁) (i : F₁ ≅ G) : HEq (transport F₀ F₁ G h i) i := by
  cases h
  rfl

end CategoryTheory.NatIsoSourceRetarget

end
end OriginalFullSource014

/-! Source body: GenericNativeSourceIsoFamilyFrame. -/
section OriginalFullSource015

set_option autoImplicit false
noncomputable section
universe uI vI uA vA uB vB
open CategoryTheory

namespace CategoryTheory.SourceIsoFamilyOfFunctorIsos

/-- Native source-op indexing and whole functor types precede all actual mapIso component values. -/
def nativeFamily {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (F G : Iᵒᵖ ⥤ A ⥤ A) (e : F ≅ G) (K : A ⥤ B) :=
  family (fun X : I => F.obj (Opposite.op X)) (fun X : I => G.obj (Opposite.op X))
    (fun X : I => e.app (Opposite.op X)) K

/-- Eliminate the complete chosen source functor equality before original native SourceIso family values. -/
theorem nativeRetarget_heq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (F₀ F₁ G : Iᵒᵖ ⥤ A ⥤ A) (hF : F₀ = F₁)
    (e : F₁ ≅ G) (K : A ⥤ B) :
    HEq (nativeFamily F₀ G (NatIsoSourceRetarget.transport F₀ F₁ G hF e) K)
      (nativeFamily F₁ G e K) := by
  cases hF
  rfl

end CategoryTheory.SourceIsoFamilyOfFunctorIsos

end
end OriginalFullSource015

/-! Source body: GenericSourceIsoFormulaTransport. -/
section OriginalFullSource016

set_option autoImplicit false
noncomputable section
universe uI uC vC
open CategoryTheory

namespace CategoryTheory.SourceIsoFormulaTransport

/-- The entire source equation is formed only after both complete Iso and source map families. -/
def Formula {I : Type uI} {C : Type uC} [Category.{vC} C]
    (X X' Y Y' : I → C) (f : ∀ a, X a ⟶ X' a) (g : ∀ a, Y a ⟶ Y' a)
    (i : ∀ a, X a ≅ Y a) (i' : ∀ a, X' a ≅ Y' a) : Prop :=
  ∀ a, f a ≫ (i' a).hom = (i a).hom ≫ g a

/-- Eliminate all complete source object/map/Iso family identities before any hom or target getter. -/
theorem transport {I : Type uI} {C : Type uC} [Category.{vC} C]
    (X₀ X₁ X'₀ X'₁ Y₀ Y₁ Y'₀ Y'₁ : I → C)
    (hX : X₀ = X₁) (hX' : X'₀ = X'₁) (hY : Y₀ = Y₁) (hY' : Y'₀ = Y'₁)
    (f₀ : ∀ a, X₀ a ⟶ X'₀ a) (f₁ : ∀ a, X₁ a ⟶ X'₁ a) (hf : HEq f₀ f₁)
    (g₀ : ∀ a, Y₀ a ⟶ Y'₀ a) (g₁ : ∀ a, Y₁ a ⟶ Y'₁ a) (hg : HEq g₀ g₁)
    (i₀ : ∀ a, X₀ a ≅ Y₀ a) (i₁ : ∀ a, X₁ a ≅ Y₁ a) (hi : HEq i₀ i₁)
    (i'₀ : ∀ a, X'₀ a ≅ Y'₀ a) (i'₁ : ∀ a, X'₁ a ≅ Y'₁ a) (hi' : HEq i'₀ i'₁)
    (proof : Formula X₀ X'₀ Y₀ Y'₀ f₀ g₀ i₀ i'₀) : Formula X₁ X'₁ Y₁ Y'₁ f₁ g₁ i₁ i'₁ := by
  cases hX
  cases hX'
  cases hY
  cases hY'
  cases hf
  cases hg
  cases hi
  cases hi'
  exact proof

end CategoryTheory.SourceIsoFormulaTransport

end
end OriginalFullSource016

/-! Source body: GenericSourceOutputComponentFormulaTransport. -/
section OriginalFullSource021

set_option autoImplicit false
noncomputable section
universe uI vI uA vA uB vB
open CategoryTheory

namespace CategoryTheory.SourceOutputComponentFormulaTransport

/-- Keep whole source and target functor families before original SourceIso type or map values. -/
def Formula {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (K : A ⥤ B)
    (F G : I → (A ⥤ A))
    (r : ∀ X X', (X' ⟶ X) → ∀ Y : A, (G X).obj Y ⟶ (G X').obj Y)
    (s : ∀ X X', (X' ⟶ X) → ∀ Y : A, (F X).obj Y ⟶ (F X').obj Y)
    (i : ∀ X Y, K.obj ((G X).obj Y) ≅ K.obj ((F X).obj Y)) : Prop :=
  ∀ (X X' : I) (f : X' ⟶ X) (Y : A),
    K.map (r X X' f Y) ≫ (i X' Y).hom = (i X Y).hom ≫ K.map (s X X' f Y)

/-- Eliminate complete source/target functor type identities before original Iso-family values and all map getters. -/
theorem transport {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B] (K : A ⥤ B)
    (F₀ F₁ G₀ G₁ : I → (A ⥤ A)) (hF : F₀ = F₁) (hG : G₀ = G₁)
    (r₀ : ∀ X X', (X' ⟶ X) → ∀ Y : A, (G₀ X).obj Y ⟶ (G₀ X').obj Y)
    (r₁ : ∀ X X', (X' ⟶ X) → ∀ Y : A, (G₁ X).obj Y ⟶ (G₁ X').obj Y) (hr : HEq r₀ r₁)
    (s₀ : ∀ X X', (X' ⟶ X) → ∀ Y : A, (F₀ X).obj Y ⟶ (F₀ X').obj Y)
    (s₁ : ∀ X X', (X' ⟶ X) → ∀ Y : A, (F₁ X).obj Y ⟶ (F₁ X').obj Y) (hs : HEq s₀ s₁)
    (i₀ : ∀ X Y, K.obj ((G₀ X).obj Y) ≅ K.obj ((F₀ X).obj Y))
    (i₁ : ∀ X Y, K.obj ((G₁ X).obj Y) ≅ K.obj ((F₁ X).obj Y)) (hi : HEq i₀ i₁)
    (proof : Formula K F₀ G₀ r₀ s₀ i₀) : Formula K F₁ G₁ r₁ s₁ i₁ := by
  cases hF
  cases hG
  cases hr
  cases hs
  cases hi
  exact proof

end CategoryTheory.SourceOutputComponentFormulaTransport

end
end OriginalFullSource021

/-! Source body: GenericSourceTransformationComponentConstructor. -/
section OriginalFullSource022

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.SourceTransformationComponentConstructor

/-- Whole source/target functor families are fixed before transforming source maps into component functions. -/
def components {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G : I → (A ⥤ A)) (m : ∀ X X' : I, (X' ⟶ X) → (G X ⟶ G X')) :=
  fun X X' : I => fun (f : X' ⟶ X) Y => (m X X' f).app Y

/-- Whole source transformation family equality is consumed before any native component map getter. -/
theorem components_eq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G : I → (A ⥤ A)) (m₀ m₁ : ∀ X X' : I, (X' ⟶ X) → (G X ⟶ G X'))
    (hm : m₀ = m₁) : components G m₀ = components G m₁ := congrArg (components G) hm

end CategoryTheory.SourceTransformationComponentConstructor

end
end OriginalFullSource022

/-! Source body: GenericBifunctorSourceComponentFamily. -/
section OriginalFullSource023

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.BifunctorSourceComponentFamily

/-- Keep the entire source component-map operation before any source/target objects or arrow are chosen. -/
def family {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (H : Iᵒᵖ ⥤ A ⥤ A) :=
  fun X X' : I => fun (f : X' ⟶ X) Y => (H.map f.op).app Y

/-- Both whole source component-map families agree after the complete bifunctor identity. -/
theorem family_heq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (H₀ H₁ : Iᵒᵖ ⥤ A ⥤ A) (hH : H₀ = H₁) : HEq (family H₀) (family H₁) := by
  cases hH
  rfl

end CategoryTheory.BifunctorSourceComponentFamily

end
end OriginalFullSource023

/-! Source body: GenericWholeComponentTypeTransport. -/
section OriginalFullSource025

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.SourceTransformationComponentConstructor

/-- Entire contravariant component-map output type family, before any maps or source objects. -/
def ComponentTypes {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G : I → (A ⥤ A)) :=
  ∀ X X', (X' ⟶ X) → ∀ Y : A, (G X).obj Y ⟶ (G X').obj Y

/-- Entire component-map output types follow whole outputFunctor identity. -/
theorem componentTypes_eq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G₀ G₁ : I → (A ⥤ A)) (hG : G₀ = G₁) : ComponentTypes G₀ = ComponentTypes G₁ :=
  congrArg ComponentTypes hG

/-- Retarget complete component values only after both entire function types are identified. -/
def retargetComponents {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G₀ G₁ : I → (A ⥤ A)) (hG : G₀ = G₁) (r : ComponentTypes G₀) : ComponentTypes G₁ := by
  cases hG
  exact r

/-- Complete component values survive retargeting after whole outputFunctor type identity. -/
theorem retargetComponents_heq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G₀ G₁ : I → (A ⥤ A)) (hG : G₀ = G₁) (r : ComponentTypes G₀) :
    HEq r (retargetComponents G₀ G₁ hG r) := by
  cases hG
  exact HEq.rfl

end CategoryTheory.SourceTransformationComponentConstructor

end
end OriginalFullSource025

/-! Source body: GenericCarrierComponentTypeFrame. -/
section OriginalFullSource026

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.SourceTransformationComponentConstructor

/-- Entire source/target carriers and category dictionaries are fixed before component output function families. -/
theorem carrierFrame_types (I₀ I₁ : Type uI) (hI : I₀ = I₁)
    (c₀ : Category.{vI} I₀) (c₁ : Category.{vI} I₁) (hc : HEq c₀ c₁)
    (A₀ A₁ : Type uA) (hA : A₀ = A₁)
    (a₀ : Category.{vA} A₀) (a₁ : Category.{vA} A₁) (ha : HEq a₀ a₁)
    (G₀ : I₀ → (@Functor A₀ a₀ A₀ a₀))
    (G₁ : I₁ → (@Functor A₁ a₁ A₁ a₁)) (hG : HEq G₀ G₁) :
    @ComponentTypes I₀ c₀ A₀ a₀ G₀ = @ComponentTypes I₁ c₁ A₁ a₁ G₁ := by
  cases hI
  cases hA
  cases hc
  cases ha
  cases hG
  rfl

end CategoryTheory.SourceTransformationComponentConstructor

end
end OriginalFullSource026

/-! Source body: GenericCarrierBifunctorComponentValueFrame. -/
section OriginalFullSource027

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.BifunctorSourceComponentFamily

/-- Consume entire source/target carriers and category dictionaries before the whole bifunctor component value. -/
theorem carrierFrame_heq (I₀ I₁ : Type uI) (hI : I₀ = I₁)
    (c₀ : Category.{vI} I₀) (c₁ : Category.{vI} I₁) (hc : HEq c₀ c₁)
    (A₀ A₁ : Type uA) (hA : A₀ = A₁)
    (a₀ : Category.{vA} A₀) (a₁ : Category.{vA} A₁) (ha : HEq a₀ a₁)
    (H₀ : @Functor (Opposite I₀) (@Category.opposite I₀ c₀) (@Functor A₀ a₀ A₀ a₀) (@Functor.category A₀ a₀ A₀ a₀))
    (H₁ : @Functor (Opposite I₁) (@Category.opposite I₁ c₁) (@Functor A₁ a₁ A₁ a₁) (@Functor.category A₁ a₁ A₁ a₁))
    (hH : HEq H₀ H₁) :
    HEq (@family I₀ c₀ A₀ a₀ H₀) (@family I₁ c₁ A₁ a₁ H₁) := by
  cases hI
  cases hA
  cases hc
  cases ha
  cases hH
  exact HEq.rfl

end CategoryTheory.BifunctorSourceComponentFamily

end
end OriginalFullSource027

/-! Source body: GenericBifunctorObjectFamily. -/
section OriginalFullSource030

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.BifunctorObjectFamily

/-- Retrieve the whole native-op-indexed object functor family only after its entire bifunctor is typed. -/
def objects {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (H : Iᵒᵖ ⥤ A ⥤ A) := fun X : I => H.obj (Opposite.op X)

/-- Whole bifunctor identity precedes every native source object functor. -/
theorem objects_eq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (H₀ H₁ : Iᵒᵖ ⥤ A ⥤ A) (hH : H₀ = H₁) : objects H₀ = objects H₁ := congrArg objects hH

end CategoryTheory.BifunctorObjectFamily

end
end OriginalFullSource030

/-! Source body: GenericCarrierTransformationComponentFrame. -/
section OriginalFullSource031

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.SourceTransformationComponentConstructor

/-- Complete source/target carrier, category and outputFunctor identities precede original transformation and component values. -/
theorem carrierFrame_heq (I₀ I₁ : Type uI) (hI : I₀ = I₁)
    (c₀ : Category.{vI} I₀) (c₁ : Category.{vI} I₁) (hc : HEq c₀ c₁)
    (A₀ A₁ : Type uA) (hA : A₀ = A₁)
    (a₀ : Category.{vA} A₀) (a₁ : Category.{vA} A₁) (ha : HEq a₀ a₁)
    (G₀ : I₀ → (@Functor A₀ a₀ A₀ a₀)) (G₁ : I₁ → (@Functor A₁ a₁ A₁ a₁)) (hG : HEq G₀ G₁)
    (m₀ : ∀ X X' : I₀, (@Quiver.Hom I₀ c₀.toCategoryStruct.toQuiver X' X) → (@NatTrans A₀ a₀ A₀ a₀ (G₀ X) (G₀ X')))
    (m₁ : ∀ X X' : I₁, (@Quiver.Hom I₁ c₁.toCategoryStruct.toQuiver X' X) → (@NatTrans A₁ a₁ A₁ a₁ (G₁ X) (G₁ X')))
    (hm : HEq m₀ m₁) : HEq (@components I₀ c₀ A₀ a₀ G₀ m₀) (@components I₁ c₁ A₁ a₁ G₁ m₁) := by
  cases hI
  cases hA
  cases hc
  cases ha
  cases hG
  cases hm
  exact HEq.rfl

end CategoryTheory.SourceTransformationComponentConstructor

end
end OriginalFullSource031

/-! Source body: GenericCompleteTargetMapFamily. -/
section OriginalFullSource032

set_option autoImplicit false
noncomputable section
universe uN uA vA uJ
open CategoryTheory
namespace CategoryTheory.CompleteTargetMapFamily

/-- Entire target map operation after both object carriers and the full target functor family. -/
def family (N : Type uN) (A : Type uA) (ca : Category.{vA} A) (J : Type uJ)
    (G : N → @Functor A ca A ca) :=
  fun (Y : N) (Z Z' : A) (f : @Quiver.Hom A ca.toCategoryStruct.toQuiver Z Z') (_a : J) => (G Y).map f

/-- Complete carrier, category, and functor family identities precede every target map getter. -/
theorem family_heq (N0 N1 : Type uN) (hN : N0 = N1)
    (A0 A1 : Type uA) (hA : A0 = A1)
    (c0 : Category.{vA} A0) (c1 : Category.{vA} A1) (hc : HEq c0 c1) (J : Type uJ)
    (G0 : N0 → @Functor A0 c0 A0 c0) (G1 : N1 → @Functor A1 c1 A1 c1) (hG : HEq G0 G1) :
    HEq (family N0 A0 c0 J G0) (family N1 A1 c1 J G1) := by
  cases hN
  cases hA
  cases hc
  cases hG
  rfl

end CategoryTheory.CompleteTargetMapFamily
end
end OriginalFullSource032

/-! Source body: GenericCompleteComponentParameterLift. -/
section OriginalFullSource040

set_option autoImplicit false
noncomputable section
universe uI vI uA vA uJ
open CategoryTheory
namespace CategoryTheory.CompleteComponentParameterLift

/-- The full native component function type retains every source, target and parameter binder. -/
def Types (I : Type uI) (ci : Category.{vI} I) (A : Type uA) (ca : Category.{vA} A)
    (J : Type uJ) (G : I → @Functor A ca A ca) :=
  ∀ (X X' : I) (Y : A), @Quiver.Hom I ci.toCategoryStruct.toQuiver X' X →
    J → @Quiver.Hom A ca.toCategoryStruct.toQuiver ((G X).obj Y) ((G X').obj Y)

/-- One whole component lift operation is declared before native objects and arrow values. -/
def lift (I : Type uI) (ci : Category.{vI} I) (A : Type uA) (ca : Category.{vA} A)
    (J : Type uJ) (G : I → @Functor A ca A ca)
    (r : @SourceTransformationComponentConstructor.ComponentTypes I ci A ca G) : Types I ci A ca J G :=
  fun X X' Y f _a => r X X' f Y

/-- Whole carrier/category/output-family identities precede the entire component lift value. -/
theorem lift_heq (I0 I1 : Type uI) (hI : I0 = I1)
    (c0 : Category.{vI} I0) (c1 : Category.{vI} I1) (hc : HEq c0 c1)
    (A0 A1 : Type uA) (hA : A0 = A1)
    (a0 : Category.{vA} A0) (a1 : Category.{vA} A1) (ha : HEq a0 a1)
    (J : Type uJ) (G0 : I0 → @Functor A0 a0 A0 a0) (G1 : I1 → @Functor A1 a1 A1 a1)
    (hG : HEq G0 G1)
    (r0 : @SourceTransformationComponentConstructor.ComponentTypes I0 c0 A0 a0 G0)
    (r1 : @SourceTransformationComponentConstructor.ComponentTypes I1 c1 A1 a1 G1)
    (hr : HEq r0 r1) : HEq (lift I0 c0 A0 a0 J G0 r0) (lift I1 c1 A1 a1 J G1 r1) := by
  cases hI
  cases hA
  cases hc
  cases ha
  cases hG
  cases hr
  rfl

end CategoryTheory.CompleteComponentParameterLift
end
end OriginalFullSource040

/-! Source body: GenericSourceTransformationTypeTransport. -/
section OriginalFullSource055

set_option autoImplicit false
noncomputable section
universe uI vI uA vA
open CategoryTheory

namespace CategoryTheory.SourceTransformationComponentConstructor

/-- Retarget the complete source transformation family output types before any precompose map value. -/
def retargetTransformations {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G₀ G₁ : I → (A ⥤ A)) (hG : G₀ = G₁)
    (m : ∀ X X' : I, (X' ⟶ X) → (G₀ X ⟶ G₀ X')) :
    ∀ X X' : I, (X' ⟶ X) → (G₁ X ⟶ G₁ X') := by
  cases hG
  exact m

/-- Complete original source transformation values survive outputFunctor family retargeting. -/
theorem retargetTransformations_heq {I : Type uI} [Category.{vI} I] {A : Type uA} [Category.{vA} A]
    (G₀ G₁ : I → (A ⥤ A)) (hG : G₀ = G₁)
    (m : ∀ X X' : I, (X' ⟶ X) → (G₀ X ⟶ G₀ X')) :
    HEq m (retargetTransformations G₀ G₁ hG m) := by
  cases hG
  rfl

end CategoryTheory.SourceTransformationComponentConstructor

end
end OriginalFullSource055
