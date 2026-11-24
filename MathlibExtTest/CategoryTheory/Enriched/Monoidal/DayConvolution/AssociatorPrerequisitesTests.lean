/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Associator
import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendTransport

/-!
# Public Day associator prerequisite clients

These clients retain the full enriched Hom actions, the original representable
weights and coefficient words, and only the stated endpoint coends.
-/

set_option autoImplicit false
noncomputable section

universe uV vV uA uB uC uD uK uI vI
open CategoryTheory MonoidalCategory Limits Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorPrerequisiteClients

attribute [local instance] Enriched.prodCategory

section PlainCoefficients

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  (F : EnrichedFunctor V A V) (G : EnrichedFunctor V B V)
  (H : EnrichedFunctor V C V)

example (X Y : (A × B) × C) :
    (Associator.productAssociator (V := V) (A := A) (B := B) (C := C)).map X Y =
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom :=
  Associator.productAssociator_map X Y

example (X Y : (A × B) × C) :
    MonoidalClosed.uncurry ((Associator.leftCoefficients F G H).map X Y) ≫
        (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).hom =
      ((α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((Associator.rightCoefficients F G H).map X Y) :=
  Associator.coefficients_naturality F G H X Y

example (X Y : (A × B) × C) :
    MonoidalClosed.uncurry ((Associator.rightCoefficients F G H).map X Y) ≫
        (α_ (F.obj Y.1.1) (G.obj Y.1.2) (H.obj Y.2)).inv =
      ((α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((Associator.leftCoefficients F G H).map X Y) :=
  Associator.coefficients_inv_naturality F G H X Y

end PlainCoefficients

section FlatGenerators

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (F G H : EnrichedFunctor V I V) (m : I)
  [HasCoproduct (AssociatorFlat.leftObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.leftRelations d F G H m)]
  [HasCoproduct (AssociatorFlat.rightObjects d F G H m)]
  [HasCoproduct (AssociatorFlat.rightRelations d F G H m)]
  [HasCoequalizer (AssociatorFlat.leftMap0 d F G H m)
    (AssociatorFlat.leftMap1 d F G H m)]
  [HasCoequalizer (AssociatorFlat.rightMap0 d F G H m)
    (AssociatorFlat.rightMap1 d F G H m)]

example (X : (I × I) × I) :
    AssociatorFlat.leftGenerator d F G H m X ≫ (AssociatorFlat.iso d F G H m).hom =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).inv m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).hom) ≫
          AssociatorFlat.rightGenerator d F G H m X := by
  fail_if_success haveI : SymmetricCategory V := inferInstance
  exact AssociatorFlat.leftGenerator_iso_hom d F G H m X

example (X : (I × I) × I) :
    AssociatorFlat.rightGenerator d F G H m X ≫ (AssociatorFlat.iso d F G H m).inv =
      (eHomWhiskerRight V (α_ X.1.1 X.1.2 X.2).hom m ⊗ₘ
        (α_ (F.obj X.1.1) (G.obj X.1.2) (H.obj X.2)).inv) ≫
          AssociatorFlat.leftGenerator d F G H m X :=
  AssociatorFlat.rightGenerator_iso_inv d F G H m X

example : (AssociatorFlat.iso d F G H m).hom ≫ (AssociatorFlat.iso d F G H m).inv =
    𝟙 (AssociatorFlat.leftPoint d F G H m) :=
  (AssociatorFlat.iso d F G H m).hom_inv_id

example : (AssociatorFlat.iso d F G H m).inv ≫ (AssociatorFlat.iso d F G H m).hom =
    𝟙 (AssociatorFlat.rightPoint d F G H m) :=
  (AssociatorFlat.iso d F G H m).inv_hom_id

end FlatGenerators

section RelativeCoendMaps

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (T : EnrichedFunctor V A B)
  (W : EnrichedFunctor V Aᵒᵖ V) (W' : EnrichedFunctor V Bᵒᵖ V)
  (Q : EnrichedFunctor V A V) (Q' : EnrichedFunctor V B V)
  (w : ∀ a, W.obj (op a) ⟶ W'.obj (op (T.obj a)))
  (q : ∀ a, Q.obj a ⟶ Q'.obj (T.obj a))
  (hW : ∀ a b,
    MonoidalClosed.uncurry (W.map (op b) (op a)) ≫ w a =
      (w b ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (W'.map (op (T.obj b)) (op (T.obj a))))
  (hQ : ∀ a b,
    MonoidalClosed.uncurry (Q.map a b) ≫ q b =
      (q a ⊗ₘ T.map a b) ≫ MonoidalClosed.uncurry (Q'.map (T.obj a) (T.obj b)))

example (a b : A) :
    Enriched.weightedCoend.face0 W Q a b ≫ Enriched.weightedCoend.Transport.objectMap T W W' Q Q' w q a =
      Enriched.weightedCoend.Transport.relationMap T W W' Q Q' w q a b ≫
        Enriched.weightedCoend.face0 W' Q' (T.obj a) (T.obj b) :=
  Enriched.weightedCoend.Transport.face0 T W W' Q Q' w q hW a b

example (a b : A) :
    Enriched.weightedCoend.face1 W Q a b ≫ Enriched.weightedCoend.Transport.objectMap T W W' Q Q' w q b =
      Enriched.weightedCoend.Transport.relationMap T W W' Q Q' w q a b ≫
        Enriched.weightedCoend.face1 W' Q' (T.obj a) (T.obj b) :=
  Enriched.weightedCoend.Transport.face1 T W W' Q Q' w q hQ a b

example (a : A)
    [HasCoproduct (Enriched.weightedCoend.objects W Q)]
    [HasCoproduct (Enriched.weightedCoend.relations W Q)]
    [HasCoequalizer (Enriched.weightedCoend.leftMap W Q) (Enriched.weightedCoend.rightMap W Q)]
    [HasCoproduct (Enriched.weightedCoend.objects W' Q')]
    [HasCoproduct (Enriched.weightedCoend.relations W' Q')]
    [HasCoequalizer (Enriched.weightedCoend.leftMap W' Q')
      (Enriched.weightedCoend.rightMap W' Q')] :
    Enriched.weightedCoend.ι W Q a ≫ Enriched.weightedCoend.Transport.map T W W' Q Q' w q hW hQ =
      (w a ⊗ₘ q a) ≫ Enriched.weightedCoend.ι W' Q' (T.obj a) :=
  Enriched.weightedCoend.Transport.ι_map T W W' Q Q' w q hW hQ a

end RelativeCoendMaps

section IdentityGenerators

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

example (a : C × D) (k : K)
    [HasCoproduct (objects T F G (T.obj a))]
    [HasCoproduct (relations T F G (T.obj a))]
    [HasCoequalizer (leftMap T F G (T.obj a)) (rightMap T F G (T.obj a))]
    [HasCoproduct (objects T F G k)] [HasCoproduct (relations T F G k)]
    [HasCoequalizer (leftMap T F G k) (rightMap T F G k)] :
    (T.obj a ⟶[V] k) ◁ AssociatorUnit.unitGenerator T F G a ≫
        MonoidalClosed.uncurry (Output.actionDesc T F G (T.obj a) k) =
      gen T F G k a :=
  AssociatorUnit.unitGenerator_action T F G a k

example (a b : C × D)
    [HasCoproduct (objects T F G (T.obj a))]
    [HasCoproduct (relations T F G (T.obj a))]
    [HasCoequalizer (leftMap T F G (T.obj a)) (rightMap T F G (T.obj a))]
    [HasCoproduct (objects T F G (T.obj b))]
    [HasCoproduct (relations T F G (T.obj b))]
    [HasCoequalizer (leftMap T F G (T.obj b)) (rightMap T F G (T.obj b))] :
    MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
        AssociatorUnit.unitGenerator T F G b =
      (AssociatorUnit.unitGenerator T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        obj T F G (T.obj a) ◁ T.map a b ≫
        MonoidalClosed.uncurry (Output.map T F G (T.obj a) (T.obj b)) :=
  AssociatorUnit.unitGenerator_naturality T F G a b

end IdentityGenerators

end CategoryTheory.EnrichedDayKernel.AssociatorPrerequisiteClients
