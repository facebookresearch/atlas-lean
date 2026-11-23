/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.QuotientProduct

/-!
# Tests for compactly generated quotient products
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

namespace MathlibExtTest.CompactlyGenerated.QuotientProductTests

#check CompactlyGenerated.prodSetoid
#check CompactlyGenerated.quotientProdHomeomorph
#check CompactlyGenerated.prodQuotientMap

section ProductSetoid

variable {X Y : CompactlyGenerated.{u, v}}
  (s : Setoid ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X))
  (t : Setoid ↥(CompactlyGenerated.compactlyGeneratedToTop.obj Y))

example (p : ↥(CompactlyGenerated.compactlyGeneratedToTop.obj (X ⊗ Y))) :
    CompactlyGenerated.prodSetoid s t p p :=
  (CompactlyGenerated.prodSetoid s t).refl' p

example (p q :
    ↥(CompactlyGenerated.compactlyGeneratedToTop.obj (X ⊗ Y)))
    (h : CompactlyGenerated.prodSetoid s t p q) :
    ∃ e : ↥(CompactlyGenerated.compactlyGeneratedToTop.obj (X ⊗ Y)) ≃
        (↥(CompactlyGenerated.compactlyGeneratedToTop.obj X) ×
          ↥(CompactlyGenerated.compactlyGeneratedToTop.obj Y)),
      s (e p).1 (e q).1 ∧ t (e p).2 (e q).2 := by
  unfold CompactlyGenerated.prodSetoid at h
  exact ⟨_, h⟩

example (p q :
    ↥(CompactlyGenerated.compactlyGeneratedToTop.obj (X ⊗ Y))) :
    CompactlyGenerated.prodSetoid
        (⊤ : Setoid ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X))
        (⊤ : Setoid ↥(CompactlyGenerated.compactlyGeneratedToTop.obj Y)) p q :=
  ⟨trivial, trivial⟩

end ProductSetoid

section Homeomorphism

variable (X Y : CompactlyGenerated.{u, v})
  (s : Setoid ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X))

example : Quotient
      (CompactlyGenerated.prodSetoid (Y := Y) s (⊥ : Setoid Y)) ≃ₜ
    ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
      ((@CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
        (@instUCompactlyGeneratedSpaceQuotient.{u, v}
          ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X) X.toTop.str s
          X.is_compactly_generated)) ⊗ Y)) :=
  CompactlyGenerated.quotientProdHomeomorph X Y s

example (z : Quotient
    (CompactlyGenerated.prodSetoid (Y := Y) s (⊥ : Setoid Y))) :
    (CompactlyGenerated.quotientProdHomeomorph X Y s).symm
        (CompactlyGenerated.quotientProdHomeomorph X Y s z) = z :=
  (CompactlyGenerated.quotientProdHomeomorph X Y s).left_inv z

example (z : ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
    ((@CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
      (@instUCompactlyGeneratedSpaceQuotient.{u, v}
        ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X) X.toTop.str s
        X.is_compactly_generated)) ⊗ Y))) :
    CompactlyGenerated.quotientProdHomeomorph X Y s
        ((CompactlyGenerated.quotientProdHomeomorph X Y s).symm z) = z :=
  (CompactlyGenerated.quotientProdHomeomorph X Y s).right_inv z

example : Quotient
      (CompactlyGenerated.prodSetoid (Y := Y)
        (⊥ : Setoid X) (⊥ : Setoid Y)) ≃ₜ
    ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
      ((CompactlyGenerated.of (Quotient (⊥ : Setoid X))) ⊗ Y)) :=
  CompactlyGenerated.quotientProdHomeomorph X Y ⊥

example : Quotient
      (CompactlyGenerated.prodSetoid (Y := Y)
        (⊤ : Setoid X) (⊥ : Setoid Y)) ≃ₜ
    ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
      ((CompactlyGenerated.of (Quotient (⊤ : Setoid X))) ⊗ Y)) :=
  CompactlyGenerated.quotientProdHomeomorph X Y ⊤

example :
    let E : CompactlyGenerated.{u, v} :=
      TopCat.toCompactlyGenerated.obj (TopCat.of (ULift.{v} PEmpty))
    Quotient (CompactlyGenerated.prodSetoid (Y := E) s (⊥ : Setoid E)) ≃ₜ
      ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
        ((@CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
          (@instUCompactlyGeneratedSpaceQuotient.{u, v}
            ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X) X.toTop.str s
            X.is_compactly_generated)) ⊗ E)) :=
  CompactlyGenerated.quotientProdHomeomorph X _ s

example :
    let P : CompactlyGenerated.{u, v} :=
      TopCat.toCompactlyGenerated.obj (TopCat.of (ULift.{v} PUnit))
    Quotient (CompactlyGenerated.prodSetoid (Y := P) s (⊥ : Setoid P)) ≃ₜ
      ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
        ((@CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
          (@instUCompactlyGeneratedSpaceQuotient.{u, v}
            ↥(CompactlyGenerated.compactlyGeneratedToTop.obj X) X.toTop.str s
            X.is_compactly_generated)) ⊗ P)) :=
  CompactlyGenerated.quotientProdHomeomorph X _ s

end Homeomorphism

section QuotientMaps

variable {W X Y Z : CompactlyGenerated.{u, v}}
  (f : W ⟶ X) (g : Y ⟶ Z)
  (hf : IsQuotientMap (ConcreteCategory.hom f))
  (hg : IsQuotientMap (ConcreteCategory.hom g))

example : IsQuotientMap (ConcreteCategory.hom (f ⊗ₘ g)) :=
  CompactlyGenerated.prodQuotientMap f g hf hg

example : IsQuotientMap (ConcreteCategory.hom (f ⊗ₘ 𝟙 Y)) :=
  CompactlyGenerated.prodQuotientMap f (𝟙 Y) hf IsQuotientMap.id

example : IsQuotientMap (ConcreteCategory.hom (𝟙 X ⊗ₘ g)) :=
  CompactlyGenerated.prodQuotientMap (𝟙 X) g IsQuotientMap.id hg

example :
    let r := Setoid.ker (ConcreteCategory.hom f)
    Quotient (CompactlyGenerated.prodSetoid (Y := Y) r (⊥ : Setoid Y)) ≃ₜ
      ↥(CompactlyGenerated.compactlyGeneratedToTop.obj
        ((CompactlyGenerated.of (Quotient r)) ⊗ Y)) :=
  CompactlyGenerated.quotientProdHomeomorph W Y _

end QuotientMaps

section Universes

example (X Y : CompactlyGenerated.{0, 0}) (s : Setoid X) :=
  CompactlyGenerated.quotientProdHomeomorph X Y s

example (X Y : CompactlyGenerated.{1, 1}) (s : Setoid X) :=
  CompactlyGenerated.quotientProdHomeomorph X Y s

example (X Y : CompactlyGenerated.{0, 1}) (s : Setoid X) :=
  CompactlyGenerated.quotientProdHomeomorph X Y s

end Universes

section PrivacyAndTrust

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.binaryKificationIso

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.curry_apply_binaryKificationIso

#guard_msgs (error, substring := true) in
#check CompactlyGenerated.prodMap_left_isQuotientMap

#print axioms CompactlyGenerated.prodSetoid
#print axioms CompactlyGenerated.quotientProdHomeomorph
#print axioms CompactlyGenerated.prodQuotientMap

end PrivacyAndTrust

end MathlibExtTest.CompactlyGenerated.QuotientProductTests
