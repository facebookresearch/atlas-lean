/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Full lifting-class closure for heterogeneous Leibniz pushouts

Both actual parametrized adjunctions extend a generating pushout-product
law to the entire two source lifting classes. The second extension uses
the flip of the same supplied pushout packet: its point, both cofans and
its corner map are retained. The three categories and all six object and
morphism universes are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [HasPushouts C₃] [HasPullbacks C₁] [HasPullbacks C₂]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂) (H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁)
  (adj : F ⊣₂ G) (adjFlip : F.flip ⊣₂ H)

include adj adjFlip in
/-- Both genuine parameter adjunctions extend the generating law over
the complete original lifting classes. -/
theorem leibnizPushout_mem_rlp_llp (I : MorphismProperty C₁) (J : MorphismProperty C₂)
    (P : MorphismProperty C₃)
    (hGen : ∀ {X Y : C₁} (f : X ⟶ Y), I f → ∀ {U V : C₂} (g : U ⟶ V), J g →
      P.rlp.llp (((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom))
    {X Y : C₁} (f : X ⟶ Y) {U V : C₂} (g : U ⟶ V)
    (hf : I.rlp.llp f) (hg : J.rlp.llp g) :
    P.rlp.llp (((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom) := by
  intro A B p hp
  have firstExtension : ∀ {X' Y' : C₁} (i : X' ⟶ Y'), I i →
      ∀ {U' V' : C₂} (j : U' ⟶ V'), J.rlp.llp j →
        HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout F i j).ι p := by
    intro X' Y' i hi U' V' j hj
    let R := Functor.PullbackObjObj.ofHasPullback G i p
    have hR : J.rlp R.π := by
      intro U₀ V₀ k hk
      exact (adj.hasLiftingProperty_iff (Functor.PushoutObjObj.ofHasPushout F i k) R).mp
        (hGen i hi k hk p hp)
    exact (adj.hasLiftingProperty_iff (Functor.PushoutObjObj.ofHasPushout F i j) R).mpr (hj R.π hR)
  let R := Functor.PullbackObjObj.ofHasPullback H g p
  have hR : I.rlp R.π := by
    intro X₀ Y₀ i hi
    exact (adjFlip.hasLiftingProperty_iff (Functor.PushoutObjObj.ofHasPushout F i g).flip R).mp
      (firstExtension i hi g hg)
  exact (adjFlip.hasLiftingProperty_iff (Functor.PushoutObjObj.ofHasPushout F f g).flip R).mpr
    (hf R.π hR)

include adj adjFlip in
/-- The full lifting-class law holds on every supplied
original pushout packet and its actual corner. -/
theorem pushoutObjObj_mem_rlp_llp (I : MorphismProperty C₁) (J : MorphismProperty C₂)
    (P : MorphismProperty C₃)
    (hGen : ∀ {X Y : C₁} (f : X ⟶ Y), I f → ∀ {U V : C₂} (g : U ⟶ V), J g →
      P.rlp.llp (((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom))
    {X Y : C₁} (f : X ⟶ Y) {U V : C₂} (g : U ⟶ V)
    (S : F.PushoutObjObj f g) (hf : I.rlp.llp f) (hg : J.rlp.llp g) : P.rlp.llp S.ι := by
  have h := leibnizPushout_mem_rlp_llp F G H adj adjFlip I J P hGen f g hf hg
  intro A B p hp
  let R := Functor.PullbackObjObj.ofHasPullback H g p
  have hh := (adjFlip.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout F f g).flip R).mp (h p hp)
  exact (adjFlip.hasLiftingProperty_iff S.flip R).mpr hh

include adj adjFlip in
/-- The same full extension applies to any given target right class, with
no target generating rank restriction. -/
theorem leibnizPushout_mem_llp (I : MorphismProperty C₁) (J : MorphismProperty C₂)
    (P : MorphismProperty C₃)
    (hGen : ∀ {X Y : C₁} (f : X ⟶ Y), I f → ∀ {U V : C₂} (g : U ⟶ V), J g →
      P.llp (((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom))
    {X Y : C₁} (f : X ⟶ Y) {U V : C₂} (g : U ⟶ V)
    (hf : I.rlp.llp f) (hg : J.rlp.llp g) :
    P.llp (((F.leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom) := by
  have h := leibnizPushout_mem_rlp_llp F G H adj adjFlip I J P.llp
    (by
      intro X₀ Y₀ i hi U₀ V₀ j hj
      rw [llp_rlp_llp]
      exact hGen i hi j hj) f g hf hg
  rwa [llp_rlp_llp] at h

end CategoryTheory.MorphismProperty
