/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.EnrichedAdjunctionHom
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uC vC uD vD

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.UnitGeneratedEnrichment

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]

/-- The actual tensor-unit separator determines the entire map from two Hom parameters. -/
theorem tensor_point_ext (hsep : IsSeparator (𝟙_ V))
    {A B Z : V} {f g : A ⊗ B ⟶ Z}
    (h : ∀ (p : 𝟙_ V ⟶ A) (q : 𝟙_ V ⟶ B),
      (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫ f =
        (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply hsep.def
  intro q
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  apply (cancel_epi (ρ_ A).inv).mp
  apply hsep.def
  intro p
  rw [rightUnitor_inv_naturality_assoc, rightUnitor_inv_naturality_assoc]
  simpa only [tensorHom_def, Category.assoc, unitors_inv_equal] using h p q

variable {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {D : Type uD} [Category.{vD} D] [EnrichedOrdinaryCategory V D]

/-- Whole continuous Hom maps preserve composition through the original ordinary functor. -/
theorem map_comp_of_points (F : C ⥤ D) (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ {X Y : C} (f : X ⟶ Y),
      eHomEquiv V f ≫ m X Y = eHomEquiv V (F.map f)) (X Y Z : C) :
    eComp V X Y Z ≫ m X Z =
      (m X Y ⊗ₘ m Y Z) ≫ eComp V (F.obj X) (F.obj Y) (F.obj Z) := by
  apply tensor_point_ext hsep
  intro p q
  let f : X ⟶ Y := (eHomEquiv V).symm p
  let g : Y ⟶ Z := (eHomEquiv V).symm q
  have hpf : eHomEquiv V f = p := (eHomEquiv V).apply_symm_apply p
  have hqg : eHomEquiv V g = q := (eHomEquiv V).apply_symm_apply q
  rw [← hpf, ← hqg]
  rw [← eHomEquiv_comp_assoc, hp, tensorHom_comp_tensorHom_assoc, hp, hp,
    ← eHomEquiv_comp, F.map_comp]

/-- The derived enriched functor has the actual original object and full Hom maps. -/
@[no_expose]
def enrichedFunctor (F : C ⥤ D) (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ {X Y : C} (f : X ⟶ Y),
      eHomEquiv V f ≫ m X Y = eHomEquiv V (F.map f)) : EnrichedFunctor V C D where
  obj := F.obj
  map := m
  map_id X := by simpa only [eHomEquiv_id, F.map_id] using hp (𝟙 X)
  map_comp X Y Z := map_comp_of_points F hsep m hp X Y Z

/-- Full object characteristic of the derived enriched functor. -/
theorem enrichedFunctor_obj (F : C ⥤ D) (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ {X Y : C} (f : X ⟶ Y),
      eHomEquiv V f ≫ m X Y = eHomEquiv V (F.map f)) (X : C) :
    (enrichedFunctor F hsep m hp).obj X = F.obj X := by rfl

/-- Full Hom characteristic of the derived enriched functor. -/
theorem enrichedFunctor_map (F : C ⥤ D) (hsep : IsSeparator (𝟙_ V))
    (m : ∀ X Y : C, (X ⟶[V] Y) ⟶ (F.obj X ⟶[V] F.obj Y))
    (hp : ∀ {X Y : C} (f : X ⟶ Y),
      eHomEquiv V f ≫ m X Y = eHomEquiv V (F.map f)) (X Y : C) :
    HEq ((enrichedFunctor F hsep m hp).map X Y) (m X Y) := by rfl

end CategoryTheory.UnitGeneratedEnrichment

namespace CategoryTheory.EnrichedAdjunctionHom.Full

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  {L : V ⥤ C} {R : C ⥤ V} (d : EnrichedAdjunctionHom.Data L R) (adj : L ⊣ R)

/-- The actual original unit and full right Hom map define the arbitrary-object adjunct. -/
@[no_expose]
def forward (X : V) (M : C) : (L.obj X ⟶[V] M) ⟶ (ihom X).obj (R.obj M) :=
  d.rightMap (L.obj X) M ≫ eHomWhiskerRight V (adj.unit.app X) (R.obj M)

/-- The actual original counit and full left Hom map define the arbitrary-object inverse. -/
@[no_expose]
def inverse (X : V) (M : C) : (ihom X).obj (R.obj M) ⟶ (L.obj X ⟶[V] M) :=
  d.leftMap X (R.obj M) ≫ eHomWhiskerLeft V (L.obj X) (adj.counit.app M)

/-- Every original adjunct morphism is retained by the entire full Hom map. -/
theorem forward_point (X : V) (M : C) (f : L.obj X ⟶ M) :
    eHomEquiv V f ≫ forward d adj X M = eHomEquiv V (adj.homEquiv X M f) := by
  change eHomEquiv V f ≫ d.rightMap (L.obj X) M ≫
    eHomWhiskerRight V (adj.unit.app X) (R.obj M) = _
  have h := congrArg (fun z => z ≫
    eHomWhiskerRight V (adj.unit.app X) (R.obj M)) (d.rightPoint f)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((eHomEquiv_comp_eHomWhiskerRight V V (adj.unit.app X) (R.map f)).trans
      (congrArg (eHomEquiv V) (adj.homEquiv_unit X M f).symm)))

/-- Every original inverse adjunct morphism is retained by the entire full Hom map. -/
theorem inverse_point (X : V) (M : C) (f : X ⟶ R.obj M) :
    eHomEquiv V f ≫ inverse d adj X M =
      eHomEquiv V ((adj.homEquiv X M).symm f) := by
  change eHomEquiv V f ≫ d.leftMap X (R.obj M) ≫
    eHomWhiskerLeft V (L.obj X) (adj.counit.app M) = _
  have h := congrArg (fun z => z ≫
    eHomWhiskerLeft V (L.obj X) (adj.counit.app M)) (d.leftPoint f)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans ((eHomEquiv_comp_eHomWhiskerLeft V C (L.map f) (adj.counit.app M)).trans
      (congrArg (eHomEquiv V) (adj.homEquiv_counit X M f).symm)))

/-- Both full original mapping-object inverse laws are derived from the actual adjunction. -/
theorem forward_inverse (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    forward d adj X M ≫ inverse d adj X M = 𝟙 _ := by
  apply hsep.def
  intro p
  let f : L.obj X ⟶ M := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := (eHomEquiv V).apply_symm_apply p
  have hf := forward_point d adj X M f
  have hg := inverse_point d adj X M (adj.homEquiv X M f)
  have hinv : eHomEquiv V ((adj.homEquiv X M).symm (adj.homEquiv X M f)) = p :=
    (congrArg (eHomEquiv V) ((adj.homEquiv X M).symm_apply_apply f)).trans hp
  change p ≫ (forward d adj X M ≫ inverse d adj X M) = p ≫ 𝟙 _
  exact (Category.assoc p (forward d adj X M) (inverse d adj X M)).symm.trans
    ((congrArg (fun z => z ≫ inverse d adj X M) ((congrArg
      (fun z => z ≫ forward d adj X M) hp).symm.trans hf)).trans
        ((hg.trans hinv).trans (Category.comp_id p).symm))

/-- Both full original evaluation-object inverse laws are derived from the actual adjunction. -/
theorem inverse_forward (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    inverse d adj X M ≫ forward d adj X M = 𝟙 _ := by
  apply hsep.def
  intro p
  let f : X ⟶ R.obj M :=
    (eHomEquiv V (C := V) (X := X) (Y := R.obj M)).symm p
  have hp : eHomEquiv V f = p :=
    (eHomEquiv V (C := V) (X := X) (Y := R.obj M)).apply_symm_apply p
  have hf := inverse_point d adj X M f
  have hg := forward_point d adj X M ((adj.homEquiv X M).symm f)
  have hinv : eHomEquiv V (adj.homEquiv X M ((adj.homEquiv X M).symm f)) = p :=
    (congrArg (eHomEquiv V) ((adj.homEquiv X M).apply_symm_apply f)).trans hp
  change p ≫ (inverse d adj X M ≫ forward d adj X M) = p ≫ 𝟙 _
  exact (Category.assoc p (inverse d adj X M) (forward d adj X M)).symm.trans
    ((congrArg (fun z => z ≫ forward d adj X M) ((congrArg
      (fun z => z ≫ inverse d adj X M) hp).symm.trans hf)).trans
        ((hg.trans hinv).trans (Category.comp_id p).symm))

/-- The actual arbitrary-object adjunction gives a whole genuine enriched Hom isomorphism. -/
@[no_expose]
def homIso (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    (L.obj X ⟶[V] M) ≅ (ihom X).obj (R.obj M) where
  hom := forward d adj X M
  inv := inverse d adj X M
  hom_inv_id := forward_inverse d adj hsep X M
  inv_hom_id := inverse_forward d adj hsep X M

/-- Full left functor enrichment is derived from the actual ordinary functor and Hom maps. -/
@[no_expose]
def leftFunctor (hsep : IsSeparator (𝟙_ V)) : EnrichedFunctor V V C :=
  UnitGeneratedEnrichment.enrichedFunctor L hsep d.leftMap d.leftPoint

/-- Full right functor enrichment is derived from the actual ordinary functor and Hom maps. -/
@[no_expose]
def rightFunctor (hsep : IsSeparator (𝟙_ V)) : EnrichedFunctor V C V :=
  UnitGeneratedEnrichment.enrichedFunctor R hsep d.rightMap d.rightPoint

/-- Full enriched target naturality retains both complete incoming Hom parameters. -/
theorem forward_target (hsep : IsSeparator (𝟙_ V)) (X : V) (M N : C) :
    eComp V (L.obj X) M N ≫ forward d adj X N =
      (forward d adj X M ⊗ₘ d.rightMap M N) ≫
        eComp V X (R.obj M) (R.obj N) := by
  apply UnitGeneratedEnrichment.tensor_point_ext hsep
  intro p q
  let f : L.obj X ⟶ M := (eHomEquiv V).symm p
  let g : M ⟶ N := (eHomEquiv V).symm q
  have hp : eHomEquiv V f = p := (eHomEquiv V).apply_symm_apply p
  have hq : eHomEquiv V g = q := (eHomEquiv V).apply_symm_apply q
  rw [← hp, ← hq]
  rw [← eHomEquiv_comp_assoc, forward_point, tensorHom_comp_tensorHom_assoc,
    forward_point, d.rightPoint, ← eHomEquiv_comp]
  exact congrArg (eHomEquiv V) (adj.homEquiv_naturality_right f g)

/-- Full enriched source naturality retains both complete incoming Hom parameters. -/
theorem forward_source (hsep : IsSeparator (𝟙_ V)) (X Y : V) (M : C) :
    (d.leftMap X Y ⊗ₘ 𝟙 (L.obj Y ⟶[V] M)) ≫
      eComp V (L.obj X) (L.obj Y) M ≫ forward d adj X M =
        (𝟙 ((ihom X).obj Y) ⊗ₘ forward d adj Y M) ≫
          eComp V X Y (R.obj M) := by
  apply UnitGeneratedEnrichment.tensor_point_ext hsep
  intro p q
  let f : X ⟶ Y := (eHomEquiv V (C := V) (X := X) (Y := Y)).symm p
  let g : L.obj Y ⟶ M := (eHomEquiv V).symm q
  have hp : eHomEquiv V f = p :=
    (eHomEquiv V (C := V) (X := X) (Y := Y)).apply_symm_apply p
  have hq : eHomEquiv V g = q := (eHomEquiv V).apply_symm_apply q
  rw [← hp, ← hq]
  rw [tensorHom_comp_tensorHom_assoc, d.leftPoint, Category.comp_id,
    ← eHomEquiv_comp_assoc, forward_point,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, forward_point,
    ← eHomEquiv_comp]
  exact congrArg (eHomEquiv V) (adj.homEquiv_naturality_left f g)

/-- The genuine left triangle retains the actual original unit, counit and full left Hom map. -/
theorem left_triangle (X : V) :
    (λ_ (𝟙_ V)).inv ≫
      ((eHomEquiv V (adj.unit.app X) ≫ d.leftMap X (R.obj (L.obj X))) ⊗ₘ
        eHomEquiv V (adj.counit.app (L.obj X))) ≫
          eComp V (L.obj X) (L.obj (R.obj (L.obj X))) (L.obj X) =
            eId V (L.obj X) := by
  rw [d.leftPoint (show X ⟶ R.obj (L.obj X) from adj.unit.app X)]
  exact (eHomEquiv_comp V
    (L.map (show X ⟶ R.obj (L.obj X) from adj.unit.app X))
    (adj.counit.app (L.obj X))).symm.trans
      ((congrArg (fun f : L.obj X ⟶ L.obj X => eHomEquiv V f)
        (adj.left_triangle_components X)).trans (eHomEquiv_id V (L.obj X)))

/-- The genuine right triangle retains the actual original unit, counit and full right Hom map. -/
theorem right_triangle (M : C) :
    (λ_ (𝟙_ V)).inv ≫
      (eHomEquiv V (adj.unit.app (R.obj M)) ⊗ₘ
        (eHomEquiv V (adj.counit.app M) ≫ d.rightMap (L.obj (R.obj M)) M)) ≫
          eComp V (R.obj M) (R.obj (L.obj (R.obj M))) (R.obj M) =
            eId V (R.obj M) := by
  rw [d.rightPoint (show L.obj (R.obj M) ⟶ M from adj.counit.app M)]
  exact (eHomEquiv_comp V (adj.unit.app (R.obj M))
    (R.map (show L.obj (R.obj M) ⟶ M from adj.counit.app M))).symm.trans
      ((congrArg (fun f : R.obj M ⟶ R.obj M => eHomEquiv V f)
        (adj.right_triangle_components M)).trans (eHomEquiv_id V (R.obj M)))

/-- Complete public characteristic of the arbitrary-object full forward map. -/
theorem forward_eq (X : V) (M : C) : forward d adj X M =
    d.rightMap (L.obj X) M ≫ eHomWhiskerRight V (adj.unit.app X) (R.obj M) := by rfl

/-- Complete public characteristic of the arbitrary-object full inverse map. -/
theorem inverse_eq (X : V) (M : C) : inverse d adj X M =
    d.leftMap X (R.obj M) ≫ eHomWhiskerLeft V (L.obj X) (adj.counit.app M) := by rfl

/-- The previously frozen tensor-unit forward map is retained exactly. -/
theorem forward_unit_eq (M : C) :
    forward d adj (𝟙_ V) M = EnrichedAdjunctionHom.forward d adj M := by
  exact (forward_eq d adj (𝟙_ V) M).trans (EnrichedAdjunctionHom.forward_eq d adj M).symm

/-- The previously frozen tensor-unit inverse map is retained exactly. -/
theorem inverse_unit_eq (M : C) :
    inverse d adj (𝟙_ V) M = EnrichedAdjunctionHom.inverse d adj M := by
  exact (inverse_eq d adj (𝟙_ V) M).trans (EnrichedAdjunctionHom.inverse_eq d adj M).symm


/-- The entire Hom isomorphism retains the actual computed forward map. -/
theorem homIso_hom (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    (homIso d adj hsep X M).hom = forward d adj X M := by rfl

/-- The entire Hom isomorphism retains the actual computed inverse map. -/
theorem homIso_inv (hsep : IsSeparator (𝟙_ V)) (X : V) (M : C) :
    (homIso d adj hsep X M).inv = inverse d adj X M := by rfl

/-- The arbitrary-object Hom isomorphism represents every original parameter object. -/
@[no_expose]
def parameterEquiv (hsep : IsSeparator (𝟙_ V)) (P X : V) (M : C) :
    (P ⟶ (L.obj X ⟶[V] M)) ≃ (P ⟶ (ihom X).obj (R.obj M)) :=
  Iso.homCongr (Iso.refl P) (homIso d adj hsep X M)

/-- The complete parameter map is the computed original forward morphism. -/
theorem parameterEquiv_apply (hsep : IsSeparator (𝟙_ V)) (P X : V) (M : C)
    (p : P ⟶ (L.obj X ⟶[V] M)) :
    parameterEquiv d adj hsep P X M p = p ≫ forward d adj X M := by
  simp only [parameterEquiv, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
    homIso_hom]

/-- The complete inverse parameter map is the computed original inverse morphism. -/
theorem parameterEquiv_symm_apply (hsep : IsSeparator (𝟙_ V)) (P X : V) (M : C)
    (p : P ⟶ (ihom X).obj (R.obj M)) :
    (parameterEquiv d adj hsep P X M).symm p = p ≫ inverse d adj X M := by
  simp only [parameterEquiv, Iso.homCongr_symm, Iso.refl_symm, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Iso.symm_hom, homIso_inv]

/-- Entire left enriched object data remains the actual ordinary free/scalar functor. -/
theorem leftFunctor_obj (hsep : IsSeparator (𝟙_ V)) (X : V) :
    (leftFunctor d hsep).obj X = L.obj X := by rfl

/-- Entire right enriched object data remains the actual ordinary evaluation functor. -/
theorem rightFunctor_obj (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (rightFunctor d hsep).obj M = R.obj M := by rfl

/-- Entire left enriched Hom data remains the actual derived continuous Hom map. -/
theorem leftFunctor_map (hsep : IsSeparator (𝟙_ V)) (X Y : V) :
    HEq ((leftFunctor d hsep).map X Y) (d.leftMap X Y) := by rfl

/-- Entire right enriched Hom data remains the actual derived continuous Hom map. -/
theorem rightFunctor_map (hsep : IsSeparator (𝟙_ V)) (M N : C) :
    HEq ((rightFunctor d hsep).map M N) (d.rightMap M N) := by rfl

/-- The actual tensor-unit adjunction mapping object evaluates to the original value. -/
@[no_expose]
def valueIso (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (L.obj (𝟙_ V) ⟶[V] M) ≅ R.obj M :=
  homIso d adj hsep (𝟙_ V) M ≪≫ MonoidalClosed.unitIsoSelf (X := R.obj M)

/-- The complete value map is original evaluation followed by the closed-unit identification. -/
theorem valueIso_hom (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (valueIso d adj hsep M).hom = forward d adj (𝟙_ V) M ≫
      (MonoidalClosed.unitIsoSelf (X := R.obj M)).hom := by rfl

/-- The complete inverse value map is the closed-unit inverse followed by original extension. -/
theorem valueIso_inv (hsep : IsSeparator (𝟙_ V)) (M : C) :
    (valueIso d adj hsep M).inv = (MonoidalClosed.unitIsoSelf (X := R.obj M)).inv ≫
      inverse d adj (𝟙_ V) M := by rfl

end CategoryTheory.EnrichedAdjunctionHom.Full

namespace CategoryTheory.Adjunction

variable {V : Type uV} [Category.{vV} V] {C : Type uC} [Category.{vC} C]
  {L : V ⥤ C} {R R' : C ⥤ V}

/-- Transport the actual complete adjunction along a proved whole right-functor equality. -/
@[no_expose]
def ofRightEq (h : R = R') (adj : L ⊣ R) : L ⊣ R' := h ▸ adj

/-- The whole adjunction data is preserved by this value transport. -/
theorem ofRightEq_heq (h : R = R') (adj : L ⊣ R) : HEq (ofRightEq h adj) adj := by
  cases h
  rfl

/-- The entire original unit map is preserved by right-endpoint transport. -/
theorem ofRightEq_unit_app (h : R = R') (adj : L ⊣ R) (X : V) :
    HEq ((ofRightEq h adj).unit.app X) (adj.unit.app X) := by
  cases h
  rfl

/-- The entire original counit map is preserved by right-endpoint transport. -/
theorem ofRightEq_counit_app (h : R = R') (adj : L ⊣ R) (M : C) :
    HEq ((ofRightEq h adj).counit.app M) (adj.counit.app M) := by
  cases h
  rfl

/-- Both full original ordinary adjunct maps are preserved by right-endpoint transport. -/
theorem ofRightEq_homEquiv (h : R = R') (adj : L ⊣ R) (X : V) (M : C) :
    HEq ((ofRightEq h adj).homEquiv X M) (adj.homEquiv X M) := by
  cases h
  rfl

end CategoryTheory.Adjunction
