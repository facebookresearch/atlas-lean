/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorFaces

/-!
# Identity insertion into the original inner Day coend

The enriched identity is inserted into the actual chosen generator.
The original full output action recovers every inner generator from it.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uC uD uK
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.AssociatorUnit

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]
  {K : Type uK} [EnrichedCategory V K]

/-- Insert the actual enriched identity as the weight factor of a generator. -/
abbrev identityInsert (x : K) (Q : V) : Q ⟶ (x ⟶[V] x) ⊗ Q :=
  (λ_ Q).inv ≫ (eId V x ⊗ₘ 𝟙 Q)

omit [BraidedCategory V] in
/-- Identity insertion preserves every actual coefficient map. -/
@[reassoc]
theorem identityInsert_naturality (x : K) {Q Q' : V} (s : Q ⟶ Q') :
    identityInsert x Q ≫ (x ⟶[V] x) ◁ s = s ≫ identityInsert x Q' := by
  simp only [identityInsert, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]

omit [BraidedCategory V] in
/-- Identity insertion retains the original coefficient associator. -/
@[reassoc]
theorem identityInsert_assoc (x : K) (R Q : V) :
    identityInsert x (R ⊗ Q) ≫ (α_ (x ⟶[V] x) R Q).inv =
      identityInsert x R ▷ Q := by
  simp only [identityInsert, tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_left]
  monoidal

/-- Enriched precomposition contracts the inserted target identity on the full Hom object. -/
@[reassoc]
theorem identityInsert_precomposition (x y : K) {R : V} (t : R ⟶ (x ⟶[V] y)) :
    identityInsert y R ≫ (y ⟶[V] y) ◁ t ≫
        (β_ (y ⟶[V] y) (x ⟶[V] y)).hom ≫ eComp V x y y = t := by
  simp only [identityInsert, ← id_tensorHom, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  rw [BraidedCategory.braiding_naturality_assoc, leftUnitor_inv_braiding_assoc,
    tensorHom_def_assoc, ← rightUnitor_inv_naturality_assoc, e_comp_id, Category.comp_id]

/-- The same complete contraction retains the whole additional coefficient tensor. -/
@[reassoc]
theorem identityInsert_precomposition_tensor (x y : K) {R : V}
    (t : R ⟶ (x ⟶[V] y)) (Q : V) :
    identityInsert y (R ⊗ Q) ≫ (α_ (y ⟶[V] y) R Q).inv ≫
        (((y ⟶[V] y) ◁ t ≫ (β_ (y ⟶[V] y) (x ⟶[V] y)).hom ≫
          eComp V x y y) ⊗ₘ 𝟙 Q) = t ⊗ₘ 𝟙 Q := by
  rw [← Category.assoc, identityInsert_assoc, tensorHom_id, ← comp_whiskerRight]
  simpa only [identityInsert, tensorHom_id, Category.assoc] using
    congrArg (fun f => f ▷ Q) (identityInsert_precomposition x y t)

@[reassoc]
private theorem identityInsert_outputWord (x y : K) (Q : V) :
    (x ⟶[V] y) ◁ identityInsert x Q ≫
        (α_ (x ⟶[V] y) (x ⟶[V] x) Q).inv ≫
        ((β_ (x ⟶[V] y) (x ⟶[V] x)).hom ⊗ₘ 𝟙 Q) =
      ((λ_ (x ⟶[V] y)).inv ≫ eId V x ▷ (x ⟶[V] y)) ▷ Q := by
  simp only [identityInsert, tensorHom_id, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, BraidedCategory.braiding_naturality_right]
  simp only [braiding_tensorUnit_right, comp_whiskerRight, Category.assoc]
  monoidal

/-- The full output Hom action contracts the inserted identity without a separator. -/
theorem identityInsert_outputAction (x y : K) (Q : V) :
    (x ⟶[V] y) ◁ identityInsert x Q ≫ Output.outputAction x x y Q =
      𝟙 ((x ⟶[V] y) ⊗ Q) := by
  simp only [Output.outputAction]
  rw [identityInsert_outputWord_assoc]
  rw [tensorHom_id, ← comp_whiskerRight]
  simp only [Category.assoc, e_id_comp, id_whiskerRight]

variable [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

/-- Inserting the output identity contracts the entire original input weight face. -/
@[reassoc]
theorem relationInsert_face0 (a b : C × D) :
    identityInsert (T.obj b) ((a ⟶[V] b) ⊗ (F.obj a.1 ⊗ G.obj a.2)) ≫
        (α_ ((weight T (T.obj b)).obj (op b)) (a ⟶[V] b)
          (F.obj a.1 ⊗ G.obj a.2)).inv ≫
        (MonoidalClosed.uncurry ((weight T (T.obj b)).map (op b) (op a)) ⊗ₘ
          𝟙 (F.obj a.1 ⊗ G.obj a.2)) =
      T.map a b ⊗ₘ 𝟙 (F.obj a.1 ⊗ G.obj a.2) := by
  rw [weight_uncurry_map]
  exact identityInsert_precomposition_tensor (T.obj a) (T.obj b) (T.map a b) _

/-- The actual identity generator into the original inner coend at its selected index value. -/
abbrev unitGenerator (a : C × D)
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))] :
    F.obj a.1 ⊗ G.obj a.2 ⟶ EnrichedDayKernel.obj T F G (T.obj a) :=
  identityInsert (T.obj a) (F.obj a.1 ⊗ G.obj a.2) ≫
    EnrichedDayKernel.gen T F G (T.obj a) a

/-- Every actual inner generator is the original full output action on its identity generator. -/
@[reassoc]
theorem unitGenerator_action (a : C × D) (k : K)
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    (T.obj a ⟶[V] k) ◁ unitGenerator T F G a ≫
        MonoidalClosed.uncurry (Output.actionDesc T F G (T.obj a) k) =
      EnrichedDayKernel.gen T F G k a := by
  let x := T.obj a
  let Q := F.obj a.1 ⊗ G.obj a.2
  let R : V := x ⟶[V] k
  let A0 := EnrichedDayKernel.obj T F G x
  let Ak := EnrichedDayKernel.obj T F G k
  let g0 : (x ⟶[V] x) ⊗ Q ⟶ A0 := EnrichedDayKernel.gen T F G x a
  let gk : R ⊗ Q ⟶ Ak := EnrichedDayKernel.gen T F G k a
  let act : R ⊗ A0 ⟶ Ak :=
    MonoidalClosed.uncurry (Output.actionDesc T F G x k)
  have hg : R ◁ g0 ≫ act = Output.outputAction x x k Q ≫ gk := by
    have h := congrArg MonoidalClosed.uncurry (Output.gen_actionDesc T F G x k a)
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry] at h
    exact h
  change R ◁ (identityInsert x Q ≫ g0) ≫ act = gk
  rw [whiskerLeft_comp, Category.assoc, hg]
  rw [← Category.assoc, identityInsert_outputAction, Category.id_comp]

/-- The full original relation at the target index preserves the identity generators. -/
theorem unitGenerator_balanced (a b : C × D)
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj b))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj b))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj b))
      (EnrichedDayKernel.rightMap T F G (T.obj b))] :
    (T.map a b ⊗ₘ 𝟙 (F.obj a.1 ⊗ G.obj a.2)) ≫
        EnrichedDayKernel.gen T F G (T.obj b) a =
      (β_ (a ⟶[V] b) (F.obj a.1 ⊗ G.obj a.2)).hom ≫
        MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
        unitGenerator T F G b := by
  let Qa := F.obj a.1 ⊗ G.obj a.2
  let Qb := F.obj b.1 ⊗ G.obj b.2
  let R : V := a ⟶[V] b
  let x := T.obj a
  let y := T.obj b
  let E : V := y ⟶[V] y
  let Y := EnrichedDayKernel.obj T F G y
  let ga : (x ⟶[V] y) ⊗ Qa ⟶ Y := EnrichedDayKernel.gen T F G y a
  let gb : E ⊗ Qb ⟶ Y := EnrichedDayKernel.gen T F G y b
  let w : E ⊗ R ⟶ (x ⟶[V] y) :=
    MonoidalClosed.uncurry ((weight T y).map (op b) (op a))
  let f : Qa ⊗ R ⟶ Qb := MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  let l : E ⊗ (R ⊗ Qa) ⟶ (x ⟶[V] y) ⊗ Qa :=
    (α_ E R Qa).inv ≫ (w ⊗ₘ 𝟙 Qa)
  let r : E ⊗ (R ⊗ Qa) ⟶ E ⊗ Qb := E ◁ ((β_ R Qa).hom ≫ f)
  have hb : l ≫ ga = r ≫ gb := EnrichedDayKernel.gen_balanced T F G y a b
  have h0 : identityInsert y (R ⊗ Qa) ≫ l = T.map a b ⊗ₘ 𝟙 Qa :=
    relationInsert_face0 T F G a b
  have h1 : identityInsert y (R ⊗ Qa) ≫ r =
      ((β_ R Qa).hom ≫ f) ≫ identityInsert y Qb :=
    identityInsert_naturality y ((β_ R Qa).hom ≫ f)
  have h0' := congrArg (fun z => z ≫ ga) h0
  have h1' := congrArg (fun z => z ≫ gb) h1
  have hb' := congrArg (fun z => identityInsert y (R ⊗ Qa) ≫ z) hb
  simp only [Category.assoc] at h0' h1' hb'
  change (T.map a b ⊗ₘ 𝟙 Qa) ≫ ga =
    (β_ R Qa).hom ≫ f ≫ identityInsert y Qb ≫ gb
  have hc := h0'.symm.trans (hb'.trans h1')
  simpa only [identityInsert, Category.assoc] using hc

/-- The identity-generator map is natural on the entire original product-enriched Hom. -/
@[reassoc]
theorem unitGenerator_naturality (a b : C × D)
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj b))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj b))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj b))
      (EnrichedDayKernel.rightMap T F G (T.obj b))] :
    MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫ unitGenerator T F G b =
      (unitGenerator T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        EnrichedDayKernel.obj T F G (T.obj a) ◁ T.map a b ≫
        MonoidalClosed.uncurry (Output.map T F G (T.obj a) (T.obj b)) := by
  let Qa := F.obj a.1 ⊗ G.obj a.2
  let Qb := F.obj b.1 ⊗ G.obj b.2
  let R : V := a ⟶[V] b
  let R' : V := T.obj a ⟶[V] T.obj b
  let A0 := EnrichedDayKernel.obj T F G (T.obj a)
  let A1 := EnrichedDayKernel.obj T F G (T.obj b)
  let ua : Qa ⟶ A0 := unitGenerator T F G a
  let ub : Qb ⟶ A1 := unitGenerator T F G b
  let t : R ⟶ R' := T.map a b
  let f : Qa ⊗ R ⟶ Qb := MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  let ga : R' ⊗ Qa ⟶ A1 := EnrichedDayKernel.gen T F G (T.obj b) a
  let act : R' ⊗ A0 ⟶ A1 :=
    MonoidalClosed.uncurry (Output.actionDesc T F G (T.obj a) (T.obj b))
  let out : A0 ⊗ R' ⟶ A1 :=
    MonoidalClosed.uncurry (Output.map T F G (T.obj a) (T.obj b))
  have hb : (t ⊗ₘ 𝟙 Qa) ≫ ga = (β_ R Qa).hom ≫ f ≫ ub :=
    unitGenerator_balanced T F G a b
  have hd : R' ◁ ua ≫ act = ga := unitGenerator_action T F G a (T.obj b)
  have hm : out = (β_ R' A0).inv ≫ act := Output.map_uncurry T F G (T.obj a) (T.obj b)
  change f ≫ ub = (ua ⊗ₘ 𝟙 R) ≫ A0 ◁ t ≫ out
  symm
  rw [hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp, Category.comp_id]
  rw [BraidedCategory.braiding_inv_naturality_assoc, tensorHom_def_assoc, hd]
  rw [← tensorHom_id, hb]
  simp only [Iso.inv_hom_id_assoc]

end CategoryTheory.EnrichedDayKernel.AssociatorUnit
