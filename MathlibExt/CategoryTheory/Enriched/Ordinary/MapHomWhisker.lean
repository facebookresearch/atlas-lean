/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic
public import MathlibExt.CategoryTheory.Enriched.GradedYoneda

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA vA uB vB

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctor

section ClosedPostcomposition

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- Full enriched Hom postcomposition maps to the actual closed target action. -/
theorem map_postcompose (F : EnrichedFunctor V A V) (a b c : A)
    (p : 𝟙_ V ⟶ (b ⟶[V] c)) :
    ((ρ_ (a ⟶[V] b)).inv ≫ (a ⟶[V] b) ◁ p ≫ eComp V a b c) ≫ F.map a c =
      F.map a b ≫ (ihom (F.obj a)).map ((eHomEquiv V).symm (p ≫ F.map b c)) := by
  let r : F.obj b ⟶ F.obj c := (eHomEquiv V).symm (p ≫ F.map b c)
  have hr : eHomEquiv V r = p ≫ F.map b c := (eHomEquiv V).apply_symm_apply _
  change _ = F.map a b ≫ (ihom (F.obj a)).map r
  rw [← MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft V (F.obj a) r]
  dsimp only [eHomWhiskerLeft]
  simp only [Category.assoc]
  rw [F.map_comp]
  simp only [Category.assoc, tensorHom_def]
  rw [whisker_exchange_assoc (F.map a b) p, ← rightUnitor_inv_naturality_assoc,
    ← whiskerLeft_comp_assoc, ← hr]

end ClosedPostcomposition

/-- An enriched functor preserves full Hom postcomposition in the underlying categories. -/
theorem map_eHomWhiskerLeft_forget
    {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
    {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
    (F : EnrichedFunctor V A B) (a b c : A)
    (q : ForgetEnrichment.of V b ⟶
      ForgetEnrichment.of V c) :
    eHomWhiskerLeft V (ForgetEnrichment.of V a) q ≫ F.map a c =
      F.map a b ≫ eHomWhiskerLeft V
        (ForgetEnrichment.of V (F.obj a)) (F.forget.map q) := by
  let H := a ⟶[V] b
  let J := F.obj a ⟶[V] F.obj b
  let p : 𝟙_ V ⟶ (b ⟶[V] c) :=
    ForgetEnrichment.homTo V q
  let r : 𝟙_ V ⟶ (F.obj b ⟶[V] F.obj c) :=
    p ≫ F.map b c
  change ((ρ_ H).inv ≫ (H ◁ p) ≫ eComp V a b c) ≫ F.map a c =
    F.map a b ≫ (ρ_ J).inv ≫ (J ◁ r) ≫ eComp V (F.obj a) (F.obj b) (F.obj c)
  simp only [Category.assoc]
  rw [F.map_comp]
  simp only [tensorHom_def, Category.assoc]
  rw [whisker_exchange_assoc (F.map a b) p, ← rightUnitor_inv_naturality_assoc,
    ← whiskerLeft_comp_assoc]

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]
  {B : Type uB} [Category.{vB} B] [EnrichedOrdinaryCategory V B]

/-- An enriched functor preserves complete Hom precomposition by each original source arrow. -/
theorem map_eHomWhiskerRight (F : EnrichedFunctor V A B) {a b : A} (f : a ⟶ b) (k : A) :
    eHomWhiskerRight V f k ≫ F.map a k =
      F.map b k ≫ eHomWhiskerRight V (F.toOrdinaryFunctor.map f) (F.obj k) := by
  let H := b ⟶[V] k
  let K := F.obj b ⟶[V] F.obj k
  let p := eHomEquiv V f
  let q := F.map a b
  let r : H ⟶ K := F.map b k
  let c := eComp V (F.obj a) (F.obj b) (F.obj k)
  let g : F.obj a ⟶ F.obj b := F.toOrdinaryFunctor.map f
  have hc := F.map_comp a b k
  have hp : p ≫ q = eHomEquiv V g := (F.toOrdinaryFunctor_map f).symm
  have ht : (p ▷ H) ≫ (q ⊗ₘ r) = (p ≫ q) ⊗ₘ r := by
    exact (congrArg (fun w => w ≫ (q ⊗ₘ r)) (tensorHom_id p H).symm).trans
      ((tensorHom_comp_tensorHom p (𝟙 H) q r).trans
        (congrArg (fun w => (p ≫ q) ⊗ₘ w) (Category.id_comp r)))
  calc
    _ = (λ_ H).inv ≫ (p ▷ H) ≫ (q ⊗ₘ r) ≫ c := by
      have h := congrArg (fun w => (λ_ H).inv ≫ (p ▷ H) ≫ w) hc
      simpa only [eHomWhiskerRight, Category.assoc] using h
    _ = (λ_ H).inv ≫ ((p ≫ q) ⊗ₘ r) ≫ c := by
      simpa only [Category.assoc] using congrArg (fun w => (λ_ H).inv ≫ w ≫ c) ht
    _ = (λ_ H).inv ≫ (eHomEquiv V g ⊗ₘ r) ≫ c :=
      congrArg (fun w => (λ_ H).inv ≫ (w ⊗ₘ r) ≫ c) hp
    _ = r ≫ (λ_ K).inv ≫ (eHomEquiv V g ▷ K) ≫ c := by
      simpa only [Category.assoc] using congrArg (fun w => w ≫ c)
        (leftUnitor_inv_comp_tensorHom (eHomEquiv V g) r)
    _ = _ := rfl

section Closed

variable [MonoidalClosed V]

/-- Full uncurried output action commutes with precomposition by an original index arrow. -/
theorem uncurry_map_eHomWhiskerRight
    (F : EnrichedFunctor V A V) {a b : A} (f : a ⟶ b) (k : A) :
    (F.obj a ◁ eHomWhiskerRight V f k) ≫ MonoidalClosed.uncurry (F.map a k) =
      (F.toOrdinaryFunctor.map f ⊗ₘ 𝟙 (b ⟶[V] k)) ≫
        MonoidalClosed.uncurry (F.map b k) := by
  let g : F.obj a ⟶ F.obj b := F.toOrdinaryFunctor.map f
  have h := congrArg MonoidalClosed.uncurry (map_eHomWhiskerRight F f k)
  have hl := MonoidalClosed.uncurry_natural_left (eHomWhiskerRight V f k) (F.map a k)
  have hr := (congrArg (fun q => MonoidalClosed.uncurry (F.map b k ≫ q))
    (MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight V g (F.obj k))).trans
      (MonoidalClosed.uncurry_pre_app (C := V) (F.obj k) (F.map b k) g)
  exact hl.symm.trans (h.trans (hr.trans
    (congrArg (fun q => q ≫ MonoidalClosed.uncurry (F.map b k))
      (tensorHom_id g (b ⟶[V] k)).symm)))

/-- An actual index isomorphism transports the entire output Hom action and coefficient. -/
theorem uncurry_map_sourceIso
    (F : EnrichedFunctor V A V) {a b : A} (e : a ≅ b) (k : A)
    {U P : V} (c : U ⟶ F.obj a) (m : P ⟶ (a ⟶[V] k)) :
    (c ⊗ₘ m) ≫ MonoidalClosed.uncurry (F.map a k) =
      ((c ≫ F.toOrdinaryFunctor.map e.hom) ⊗ₘ
        (m ≫ eHomWhiskerRight V e.inv k)) ≫ MonoidalClosed.uncurry (F.map b k) := by
  let H := a ⟶[V] k
  let K := b ⟶[V] k
  let p := eHomWhiskerRight V e.hom k
  let q := eHomWhiskerRight V e.inv k
  let f : F.obj a ⟶ F.obj b := F.toOrdinaryFunctor.map e.hom
  let x := MonoidalClosed.uncurry (F.map a k)
  let y := MonoidalClosed.uncurry (F.map b k)
  have hi : q ≫ p = 𝟙 H :=
    (eHomWhiskerRightIso V A e (Y := k)).inv_hom_id
  have hn := uncurry_map_eHomWhiskerRight F e.hom k
  have h := congrArg (fun w => (F.obj a ◁ q) ≫ w) hn
  have hl : (F.obj a ◁ q) ≫ (F.obj a ◁ p) ≫ x = x := by
    rw [← whiskerLeft_comp_assoc, hi, whiskerLeft_id, Category.id_comp]
  have ht : (F.obj a ◁ q) ≫ (f ⊗ₘ 𝟙 K) = f ⊗ₘ q := by
    exact (congrArg (fun w => (F.obj a ◁ q) ≫ w) (tensorHom_id f K)).trans
      (tensorHom_def' f q).symm
  have h' : x = (f ⊗ₘ q) ≫ y := by
    exact hl.symm.trans (h.trans
      ((Category.assoc (F.obj a ◁ q) (f ⊗ₘ 𝟙 K) y).symm.trans
        (congrArg (fun w => w ≫ y) ht)))
  exact (congrArg (fun w => (c ⊗ₘ m) ≫ w) h').trans
    ((Category.assoc (c ⊗ₘ m) (f ⊗ₘ q) y).symm.trans
      (congrArg (fun w => w ≫ y) (tensorHom_comp_tensorHom c m f q)))

end Closed


end CategoryTheory.EnrichedFunctor
