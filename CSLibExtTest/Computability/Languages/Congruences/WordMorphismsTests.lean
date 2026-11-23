/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.WordMorphisms
public import CSLibExt.Computability.Languages.RegularHomImage
public import CSLibExt.Computability.Languages.ContextFree.InverseHom

/-! # Client tests for upstream word-morphism bridges -/

@[expose] public section

open scoped Computability

namespace Cslib.Language.WordMorphismsTests

universe u v

variable {Source : Type u} {Target : Type v}

example (σ : FreeMonoid Source →* FreeMonoid Target) (x y : List Source) :
    Language.Hom.ofFreeMonoidHom σ (x ++ y) =
      Language.Hom.ofFreeMonoidHom σ x ++ Language.Hom.ofFreeMonoidHom σ y :=
  Language.Hom.map_append _ _ _

example (σ : FreeMonoid Source →* FreeMonoid Target) :
    Language.Hom.ofFreeMonoidHom σ [] = [] :=
  Language.Hom.map_nil _

example (σ : FreeMonoid Source →* FreeMonoid Target) (L : Language Target) :
    wordMorphismPreimage σ L = L.preimage (Language.Hom.ofFreeMonoidHom σ) :=
  wordMorphismPreimage_eq_preimage σ L

example (f : Source → Target) (L : Language Target) :
    alphabetPreimage f L = L.preimage (List.map f) :=
  alphabetPreimage_eq_preimage f L

example (σ : FreeMonoid Source →* FreeMonoid Target) (L : Language Target)
    (x : List Source) :
    x ∈ wordMorphismPreimage σ L ↔ FreeMonoid.toList (σ (FreeMonoid.ofList x)) ∈ L := by
  simp

example (L : Language Source) :
    wordMorphismPreimage (MonoidHom.id (FreeMonoid Source)) L = L := by
  simp

example (f : Source → Target) (L : Language Target) (x : List Source) :
    x ∈ alphabetPreimage f L ↔ x.map f ∈ L := by
  simp

example (L : Language Source) : alphabetPreimage id L = L := by
  simp

example (σ : FreeMonoid Source →* FreeMonoid Target) {L : Language Target}
    (h : L.IsRegular) : (wordMorphismPreimage σ L).IsRegular :=
  Cslib.Language.IsRegular.wordMorphismPreimage h σ

example (f : Source → Target) {L : Language Target} (h : L.IsRegular) :
    (alphabetPreimage f L).IsRegular :=
  Cslib.Language.IsRegular.alphabetPreimage h f

example [Finite Source] (φ : Source → List Target) {L : Language Source}
    (h : L.IsRegular) : (L.image (Language.Hom.lift φ)).IsRegular := by
  rw [← homImage_eq_image]
  exact Cslib.Language.IsRegular.homImage h φ

example (φ : Source → List Target) {L : Language Source} (h : L.IsContextFree) :
    (L.image (Language.Hom.lift φ)).IsContextFree := by
  rw [← homImage_eq_image]
  exact Cslib.Language.IsContextFree.homImage h φ

example [Finite Source] (σ : FreeMonoid Source →* FreeMonoid Target)
    {L : Language Target} (h : L.IsContextFree) :
    (L.preimage (Language.Hom.ofFreeMonoidHom σ)).IsContextFree := by
  rw [← wordMorphismPreimage_eq_preimage]
  exact Cslib.Language.IsContextFree.preimage_wordMorphism h σ

/-- The morphism erasing every letter. -/
def erase : FreeMonoid Bool →* FreeMonoid Bool where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := rfl

example : [true, false] ∈ wordMorphismPreimage erase (1 : Language Bool) :=
  rfl

example : wordMorphismPreimage erase (0 : Language Bool) = 0 :=
  rfl

example : ({[true, false]} : Language Bool).image
    (Language.Hom.lift fun _ : Bool => ([] : List Bool)) = ({[]} : Language Bool) := by
  rw [Language.image_singleton]
  rfl

example : ({[true, false]} : Language Bool).image
    (Language.Hom.lift fun b => if b then [false, false] else [true]) =
      {[false, false, true]} := by
  rw [Language.image_singleton]
  rfl

example : [true, false] ∈ wordMorphismPreimage (FreeMonoid.map Bool.not)
    ({[false, true]} : Language Bool) :=
  rfl

example : ([] : List PEmpty) ∈
    wordMorphismPreimage (MonoidHom.id (FreeMonoid PEmpty)) (1 : Language PEmpty) :=
  rfl

example : (alphabetPreimage (fun _ : ℕ => true) (1 : Language Bool)).IsRegular :=
  IsRegular.alphabetPreimage IsRegular.one _

#print axioms Language.Hom.ofFreeMonoidHom
#print axioms wordMorphismPreimage_eq_preimage
#print axioms homImage_eq_image
#print axioms IsRegular.wordMorphismPreimage
#print axioms IsRegular.alphabetPreimage

end Cslib.Language.WordMorphismsTests
