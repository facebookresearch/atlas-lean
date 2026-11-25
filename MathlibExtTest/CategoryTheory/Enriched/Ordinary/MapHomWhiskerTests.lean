/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua

import MathlibExt.CategoryTheory.Enriched.Ordinary.MapHomWhisker

set_option autoImplicit false
noncomputable section
universe uV vV uA vA uB vB

namespace MathlibExtTest.EnrichedMapHomWhisker

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

section ClosedPostcomposition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

-- This generic client imports only the canonical enriched-functor API.
example (F : EnrichedFunctor V A V) (a b c : A)
    (p : 𝟙_ V ⟶ (b ⟶[V] c)) :
    ((ρ_ (a ⟶[V] b)).inv ≫ (a ⟶[V] b) ◁ p ≫ eComp V a b c) ≫ F.map a c =
      F.map a b ≫ (ihom (F.obj a)).map ((eHomEquiv V).symm (p ≫ F.map b c)) :=
  EnrichedFunctor.map_postcompose F a b c p

#check @EnrichedFunctor.map_postcompose
#print axioms EnrichedFunctor.map_postcompose

end ClosedPostcomposition

section ForgottenPostcomposition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]

-- No ordinary-category or closedness premise is needed for the original Hom law.
example (F : EnrichedFunctor V A B) (a b c : A)
    (q : ForgetEnrichment.of V b ⟶ ForgetEnrichment.of V c) :
    eHomWhiskerLeft V (ForgetEnrichment.of V a) q ≫ F.map a c =
      F.map a b ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj a)) (F.forget.map q) :=
  EnrichedFunctor.map_eHomWhiskerLeft_forget F a b c q

end ForgottenPostcomposition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]
  {B : Type uB} [Category.{vB} B] [EnrichedOrdinaryCategory V B]

-- Source, target, and value categories retain independent object/Hom universes.
example (F : EnrichedFunctor V A B) {a b : A} (f : a ⟶ b) (k : A) :
    eHomWhiskerRight V f k ≫ F.map a k =
      F.map b k ≫ eHomWhiskerRight V (F.toOrdinaryFunctor.map f) (F.obj k) :=
  EnrichedFunctor.map_eHomWhiskerRight F f k

example (F : EnrichedFunctor V A B) {a b c : A} (f : a ⟶ b) (g : b ⟶ c) (k : A) :
    eHomWhiskerRight V (f ≫ g) k ≫ F.map a k =
      F.map c k ≫ eHomWhiskerRight V (F.toOrdinaryFunctor.map (f ≫ g)) (F.obj k) :=
  EnrichedFunctor.map_eHomWhiskerRight F (f ≫ g) k

section Closed

variable [MonoidalClosed V]

example (F : EnrichedFunctor V A V) {a b : A} (f : a ⟶ b) (k : A) :
    (F.obj a ◁ eHomWhiskerRight V f k) ≫ MonoidalClosed.uncurry (F.map a k) =
      (F.toOrdinaryFunctor.map f ⊗ₘ 𝟙 (b ⟶[V] k)) ≫
        MonoidalClosed.uncurry (F.map b k) :=
  EnrichedFunctor.uncurry_map_eHomWhiskerRight F f k

example (F : EnrichedFunctor V A V) {a b : A} (e : a ≅ b) (k : A)
    {U P : V} (c : U ⟶ F.obj a) (m : P ⟶ (a ⟶[V] k)) :
    (c ⊗ₘ m) ≫ MonoidalClosed.uncurry (F.map a k) =
      ((c ≫ F.toOrdinaryFunctor.map e.hom) ⊗ₘ
        (m ≫ eHomWhiskerRight V e.inv k)) ≫ MonoidalClosed.uncurry (F.map b k) :=
  EnrichedFunctor.uncurry_map_sourceIso F e k c m

-- Identity coefficients expose the transported action on its entire Hom domain.
example (F : EnrichedFunctor V A V) {a b : A} (e : a ≅ b) (k : A) :
    MonoidalClosed.uncurry (F.map a k) =
      (F.toOrdinaryFunctor.map e.hom ⊗ₘ eHomWhiskerRight V e.inv k) ≫
        MonoidalClosed.uncurry (F.map b k) := by
  let f : F.obj a ⟶ F.obj b := F.toOrdinaryFunctor.map e.hom
  have h : (𝟙 (F.obj a) ⊗ₘ 𝟙 (a ⟶[V] k)) ≫ MonoidalClosed.uncurry (F.map a k) =
      ((𝟙 (F.obj a) ≫ f) ⊗ₘ (𝟙 (a ⟶[V] k) ≫ eHomWhiskerRight V e.inv k)) ≫
        MonoidalClosed.uncurry (F.map b k) :=
    EnrichedFunctor.uncurry_map_sourceIso F e k (𝟙 (F.obj a)) (𝟙 (a ⟶[V] k))
  simp only [id_tensorHom_id, Category.id_comp] at h
  dsimp only [f] at h
  exact h

end Closed

#check @EnrichedFunctor.map_eHomWhiskerRight
#check @EnrichedFunctor.uncurry_map_sourceIso
#print axioms EnrichedFunctor.map_eHomWhiskerRight
#print axioms EnrichedFunctor.uncurry_map_eHomWhiskerRight
#print axioms EnrichedFunctor.uncurry_map_sourceIso

end MathlibExtTest.EnrichedMapHomWhisker
