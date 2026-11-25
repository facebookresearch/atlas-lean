/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Left-proper gluing for maps of pushout squares

In a left proper model category, a pointwise weak equivalence between two
walking spans induces a weak equivalence between arbitrary chosen pushouts
when the same designated leg in both spans is a cofibration.

The proof factors only the non-designated target leg, uses pushout pasting and
two-out-of-three, and then transports the canonical pushout result to the
chosen squares. It makes no object-cofibrancy, Reedy, selected-category, or
arbitrary-pushout claim and installs no instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]

private theorem weakEquivalence_pushoutMap_of_fst
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    {u₀ : P₀ ⟶ Q₀} {v₀ : P₀ ⟶ R₀}
    {u₁ : P₁ ⟶ Q₁} {v₁ : P₁ ⟶ R₁}
    {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
    (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)
    [Cofibration u₀] [Cofibration u₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) := by
  let L := pushout u₀ wP
  let lQ : Q₀ ⟶ L := pushout.inl u₀ wP
  let lP : P₁ ⟶ L := pushout.inr u₀ wP
  let lambda : L ⟶ Q₁ := pushout.desc wQ u₁ hu
  have hlQ : lQ ≫ lambda = wQ := by
    dsimp only [lQ, lambda]
    rw [pushout.inl_desc]
  have hlP : lP ≫ lambda = u₁ := by
    dsimp only [lP, lambda]
    rw [pushout.inr_desc]
  let _ : Cofibration lP := by
    dsimp only [lP]
    infer_instance
  let _ : WeakEquivalence lQ :=
    IsLeftProper.weakEquivalence_of_isPushout
      (IsPushout.of_hasPushout u₀ wP)
  let _ : WeakEquivalence lambda := by
    have : WeakEquivalence (lQ ≫ lambda) := by
      rw [hlQ]
      infer_instance
    exact weakEquivalence_of_precomp lQ lambda
  let d := factorizationData (cofibrations C) (trivialFibrations C) v₁
  let k : P₁ ⟶ d.Z := d.i
  let q : d.Z ⟶ R₁ := d.p
  have hkq : k ≫ q = v₁ := d.fac
  let _ : Cofibration k := (cofibration_iff k).2 d.hi
  have hq := (mem_trivialFibrations_iff q).1 d.hp
  let _ : WeakEquivalence q := hq.2
  let m : pushout lP k ⟶ pushout u₁ k :=
    pushout.map lP k u₁ k lambda (𝟙 _) (𝟙 _)
      (by simpa using hlP) (by simp)
  let a : pushout lP k ⟶ pushout lP v₁ :=
    pushout.map lP k lP v₁ (𝟙 _) q (𝟙 _)
      (by simp) (by simpa using hkq)
  let b : pushout u₁ k ⟶ pushout u₁ v₁ :=
    pushout.map u₁ k u₁ v₁ (𝟙 _) q (𝟙 _)
      (by simp) (by simpa using hkq)
  let n : pushout lP v₁ ⟶ pushout u₁ v₁ :=
    pushout.map lP v₁ u₁ v₁ lambda (𝟙 _) (𝟙 _)
      (by simpa using hlP) (by simp)
  have hmL : pushout.inl lP k ≫ m =
      lambda ≫ pushout.inl u₁ k := by
    dsimp only [m, pushout.map]
    rw [pushout.inl_desc]
  have hmZ : pushout.inr lP k ≫ m = pushout.inr u₁ k := by
    dsimp only [m, pushout.map]
    rw [pushout.inr_desc, Category.id_comp]
  have hmOuter : IsPushout (lP ≫ lambda) k
      (pushout.inl u₁ k) (pushout.inr lP k ≫ m) := by
    rw [hlP, hmZ]
    exact IsPushout.of_hasPushout u₁ k
  have hmSq : IsPushout (pushout.inl lP k) lambda m
      (pushout.inl u₁ k) :=
    (IsPushout.of_left hmOuter hmL.symm
      (IsPushout.of_hasPushout lP k)).flip
  let _ : Cofibration (pushout.inl lP k) := by infer_instance
  let _ : WeakEquivalence m :=
    IsLeftProper.weakEquivalence_of_isPushout hmSq
  have haL : pushout.inl lP k ≫ a = pushout.inl lP v₁ := by
    dsimp only [a, pushout.map]
    rw [pushout.inl_desc, Category.id_comp]
  have haZ : pushout.inr lP k ≫ a =
      q ≫ pushout.inr lP v₁ := by
    dsimp only [a, pushout.map]
    rw [pushout.inr_desc]
  have haOuter : IsPushout lP (k ≫ q)
      (pushout.inl lP k ≫ a) (pushout.inr lP v₁) := by
    rw [hkq, haL]
    exact IsPushout.of_hasPushout lP v₁
  have haSq : IsPushout (pushout.inr lP k) q a
      (pushout.inr lP v₁) :=
    IsPushout.of_top haOuter haZ (IsPushout.of_hasPushout lP k)
  let _ : Cofibration (pushout.inr lP k) := by infer_instance
  let _ : WeakEquivalence a :=
    IsLeftProper.weakEquivalence_of_isPushout haSq
  have hbQ : pushout.inl u₁ k ≫ b = pushout.inl u₁ v₁ := by
    dsimp only [b, pushout.map]
    rw [pushout.inl_desc, Category.id_comp]
  have hbZ : pushout.inr u₁ k ≫ b =
      q ≫ pushout.inr u₁ v₁ := by
    dsimp only [b, pushout.map]
    rw [pushout.inr_desc]
  have hbOuter : IsPushout u₁ (k ≫ q)
      (pushout.inl u₁ k ≫ b) (pushout.inr u₁ v₁) := by
    rw [hkq, hbQ]
    exact IsPushout.of_hasPushout u₁ v₁
  have hbSq : IsPushout (pushout.inr u₁ k) q b
      (pushout.inr u₁ v₁) :=
    IsPushout.of_top hbOuter hbZ (IsPushout.of_hasPushout u₁ k)
  let _ : Cofibration (pushout.inr u₁ k) := by infer_instance
  let _ : WeakEquivalence b :=
    IsLeftProper.weakEquivalence_of_isPushout hbSq
  have hnL : pushout.inl lP v₁ ≫ n =
      lambda ≫ pushout.inl u₁ v₁ := by
    dsimp only [n, pushout.map]
    rw [pushout.inl_desc]
  have hnR : pushout.inr lP v₁ ≫ n = pushout.inr u₁ v₁ := by
    dsimp only [n, pushout.map]
    rw [pushout.inr_desc, Category.id_comp]
  have hmn : m ≫ b = a ≫ n := by
    apply (IsPushout.of_hasPushout lP k).hom_ext
    · calc
        pushout.inl lP k ≫ m ≫ b =
            (pushout.inl lP k ≫ m) ≫ b :=
          (Category.assoc _ _ _).symm
        _ = (lambda ≫ pushout.inl u₁ k) ≫ b := by rw [hmL]
        _ = lambda ≫ pushout.inl u₁ k ≫ b := Category.assoc _ _ _
        _ = lambda ≫ pushout.inl u₁ v₁ := by rw [hbQ]
        _ = pushout.inl lP v₁ ≫ n := hnL.symm
        _ = (pushout.inl lP k ≫ a) ≫ n := by rw [haL]
        _ = pushout.inl lP k ≫ a ≫ n := Category.assoc _ _ _
    · calc
        pushout.inr lP k ≫ m ≫ b =
            (pushout.inr lP k ≫ m) ≫ b :=
          (Category.assoc _ _ _).symm
        _ = pushout.inr u₁ k ≫ b := by rw [hmZ]
        _ = q ≫ pushout.inr u₁ v₁ := hbZ
        _ = q ≫ pushout.inr lP v₁ ≫ n := by rw [hnR]
        _ = (q ≫ pushout.inr lP v₁) ≫ n :=
          (Category.assoc _ _ _).symm
        _ = (pushout.inr lP k ≫ a) ≫ n := by rw [haZ]
        _ = pushout.inr lP k ≫ a ≫ n := Category.assoc _ _ _
  let _ : WeakEquivalence n := by
    have : WeakEquivalence (a ≫ n) := by
      rw [← hmn]
      infer_instance
    exact weakEquivalence_of_precomp a n
  let a₀ : pushout u₀ v₀ ⟶ pushout lP v₁ :=
    pushout.map u₀ v₀ lP v₁ lQ wR wP
      (pushout.condition : u₀ ≫ lQ = wP ≫ lP) hv
  have ha₀Q : pushout.inl u₀ v₀ ≫ a₀ =
      lQ ≫ pushout.inl lP v₁ := by
    dsimp only [a₀, pushout.map]
    rw [pushout.inl_desc]
  have ha₀R : pushout.inr u₀ v₀ ≫ a₀ =
      wR ≫ pushout.inr lP v₁ := by
    dsimp only [a₀, pushout.map]
    rw [pushout.inr_desc]
  have ha₀Paste : IsPushout u₀ (wP ≫ v₁)
      (lQ ≫ pushout.inl lP v₁) (pushout.inr lP v₁) :=
    (IsPushout.of_hasPushout u₀ wP).paste_vert
      (IsPushout.of_hasPushout lP v₁)
  have ha₀Outer : IsPushout (v₀ ≫ wR) u₀
      (pushout.inr lP v₁) (pushout.inl u₀ v₀ ≫ a₀) := by
    rw [hv, ha₀Q]
    exact ha₀Paste.flip
  have ha₀Sq : IsPushout (pushout.inr u₀ v₀) wR a₀
      (pushout.inr lP v₁) :=
    (IsPushout.of_left ha₀Outer ha₀R.symm
      (IsPushout.of_hasPushout u₀ v₀).flip).flip
  let _ : Cofibration (pushout.inr u₀ v₀) := by infer_instance
  let _ : WeakEquivalence a₀ :=
    IsLeftProper.weakEquivalence_of_isPushout ha₀Sq
  let alpha : pushout u₀ v₀ ⟶ pushout u₁ v₁ :=
    pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv
  have halphaQ : pushout.inl u₀ v₀ ≫ alpha =
      wQ ≫ pushout.inl u₁ v₁ := by
    dsimp only [alpha, pushout.map]
    rw [pushout.inl_desc]
  have halphaR : pushout.inr u₀ v₀ ≫ alpha =
      wR ≫ pushout.inr u₁ v₁ := by
    dsimp only [alpha, pushout.map]
    rw [pushout.inr_desc]
  have hcomp : a₀ ≫ n = alpha := by
    apply (IsPushout.of_hasPushout u₀ v₀).hom_ext
    · calc
        pushout.inl u₀ v₀ ≫ a₀ ≫ n =
            (pushout.inl u₀ v₀ ≫ a₀) ≫ n :=
          (Category.assoc _ _ _).symm
        _ = (lQ ≫ pushout.inl lP v₁) ≫ n := by rw [ha₀Q]
        _ = lQ ≫ pushout.inl lP v₁ ≫ n := Category.assoc _ _ _
        _ = lQ ≫ lambda ≫ pushout.inl u₁ v₁ := by rw [hnL]
        _ = (lQ ≫ lambda) ≫ pushout.inl u₁ v₁ :=
          (Category.assoc _ _ _).symm
        _ = wQ ≫ pushout.inl u₁ v₁ := by rw [hlQ]
        _ = pushout.inl u₀ v₀ ≫ alpha := halphaQ.symm
    · calc
        pushout.inr u₀ v₀ ≫ a₀ ≫ n =
            (pushout.inr u₀ v₀ ≫ a₀) ≫ n :=
          (Category.assoc _ _ _).symm
        _ = (wR ≫ pushout.inr lP v₁) ≫ n := by rw [ha₀R]
        _ = wR ≫ pushout.inr lP v₁ ≫ n := Category.assoc _ _ _
        _ = wR ≫ pushout.inr u₁ v₁ := by rw [hnR]
        _ = pushout.inr u₀ v₀ ≫ alpha := halphaR.symm
  change WeakEquivalence alpha
  rw [← hcomp]
  infer_instance

private theorem weakEquivalence_pushoutMap_of_snd
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    {u₀ : P₀ ⟶ Q₀} {v₀ : P₀ ⟶ R₀}
    {u₁ : P₁ ⟶ Q₁} {v₁ : P₁ ⟶ R₁}
    {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
    (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)
    [Cofibration v₀] [Cofibration v₁]
    [WeakEquivalence wP] [WeakEquivalence wQ] [WeakEquivalence wR] :
    WeakEquivalence
      (pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv) := by
  let beta : pushout v₀ u₀ ⟶ pushout v₁ u₁ :=
    pushout.map v₀ u₀ v₁ u₁ wR wQ wP hv hu
  let _ : WeakEquivalence beta :=
    weakEquivalence_pushoutMap_of_fst hv hu
  let e₀ : pushout u₀ v₀ ⟶ pushout v₀ u₀ :=
    (pushoutSymmetry u₀ v₀).hom
  let e₁ : pushout v₁ u₁ ⟶ pushout u₁ v₁ :=
    (pushoutSymmetry u₁ v₁).inv
  let alpha : pushout u₀ v₀ ⟶ pushout u₁ v₁ :=
    pushout.map u₀ v₀ u₁ v₁ wQ wR wP hu hv
  have hbetaL : pushout.inl v₀ u₀ ≫ beta =
      wR ≫ pushout.inl v₁ u₁ := by
    dsimp only [beta, pushout.map]
    rw [pushout.inl_desc]
  have hbetaR : pushout.inr v₀ u₀ ≫ beta =
      wQ ≫ pushout.inr v₁ u₁ := by
    dsimp only [beta, pushout.map]
    rw [pushout.inr_desc]
  have halphaL : pushout.inl u₀ v₀ ≫ alpha =
      wQ ≫ pushout.inl u₁ v₁ := by
    dsimp only [alpha, pushout.map]
    rw [pushout.inl_desc]
  have halphaR : pushout.inr u₀ v₀ ≫ alpha =
      wR ≫ pushout.inr u₁ v₁ := by
    dsimp only [alpha, pushout.map]
    rw [pushout.inr_desc]
  have h : e₀ ≫ beta ≫ e₁ = alpha := by
    apply (IsPushout.of_hasPushout u₀ v₀).hom_ext
    · calc
        pushout.inl u₀ v₀ ≫ e₀ ≫ beta ≫ e₁ =
            ((pushout.inl u₀ v₀ ≫ e₀) ≫ beta) ≫ e₁ := by
          simp only [Category.assoc]
        _ = (pushout.inr v₀ u₀ ≫ beta) ≫ e₁ := by
          rw [inl_comp_pushoutSymmetry_hom]
        _ = (wQ ≫ pushout.inr v₁ u₁) ≫ e₁ := by rw [hbetaR]
        _ = wQ ≫ pushout.inr v₁ u₁ ≫ e₁ := Category.assoc _ _ _
        _ = wQ ≫ pushout.inl u₁ v₁ := by
          dsimp only [e₁]
          rw [inr_comp_pushoutSymmetry_inv]
        _ = pushout.inl u₀ v₀ ≫ alpha := halphaL.symm
    · calc
        pushout.inr u₀ v₀ ≫ e₀ ≫ beta ≫ e₁ =
            ((pushout.inr u₀ v₀ ≫ e₀) ≫ beta) ≫ e₁ := by
          simp only [Category.assoc]
        _ = (pushout.inl v₀ u₀ ≫ beta) ≫ e₁ := by
          rw [inr_comp_pushoutSymmetry_hom]
        _ = (wR ≫ pushout.inl v₁ u₁) ≫ e₁ := by rw [hbetaL]
        _ = wR ≫ pushout.inl v₁ u₁ ≫ e₁ := Category.assoc _ _ _
        _ = wR ≫ pushout.inr u₁ v₁ := by
          dsimp only [e₁]
          rw [inl_comp_pushoutSymmetry_inv]
        _ = pushout.inr u₀ v₀ ≫ alpha := halphaR.symm
  change WeakEquivalence alpha
  rw [← h]
  infer_instance

/-- A map between two chosen pushout squares is a weak equivalence when the
first leg in each span is a cofibration and all three maps of span objects are
weak equivalences. -/
theorem IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    {A B X P A' B' X' P' : C}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Cofibration i] [Cofibration i']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence d := by
  let h₀ := IsPushout.of_hasPushout i g
  let h₁ := IsPushout.of_hasPushout i' g'
  let m : pushout i g ⟶ pushout i' g' :=
    pushout.map i g i' g' b c a hi hg
  let _ : WeakEquivalence m := weakEquivalence_pushoutMap_of_fst hi hg
  let e₀ : pushout i g ≅ P := h₀.isoIsPushout _ _ sq
  let e₁ : pushout i' g' ≅ P' := h₁.isoIsPushout _ _ sq'
  have hd : e₀.inv ≫ m ≫ e₁.hom = d := by
    apply sq.hom_ext
    · calc
        p ≫ (e₀.inv ≫ m ≫ e₁.hom) =
            (p ≫ e₀.inv) ≫ m ≫ e₁.hom := by simp only [Category.assoc]
        _ = pushout.inl i g ≫ m ≫ e₁.hom := by
          rw [h₀.inl_isoIsPushout_inv]
        _ = (pushout.inl i g ≫ m) ≫ e₁.hom :=
          (Category.assoc _ _ _).symm
        _ = (b ≫ pushout.inl i' g') ≫ e₁.hom := by
          apply congrArg (fun z => z ≫ e₁.hom)
          dsimp only [m, pushout.map]
          exact pushout.inl_desc _ _ _
        _ = b ≫ pushout.inl i' g' ≫ e₁.hom := Category.assoc _ _ _
        _ = b ≫ p' := by rw [h₁.inl_isoIsPushout_hom]
        _ = p ≫ d := hp.symm
    · calc
        q ≫ (e₀.inv ≫ m ≫ e₁.hom) =
            (q ≫ e₀.inv) ≫ m ≫ e₁.hom := by simp only [Category.assoc]
        _ = pushout.inr i g ≫ m ≫ e₁.hom := by
          rw [h₀.inr_isoIsPushout_inv]
        _ = (pushout.inr i g ≫ m) ≫ e₁.hom :=
          (Category.assoc _ _ _).symm
        _ = (c ≫ pushout.inr i' g') ≫ e₁.hom := by
          apply congrArg (fun z => z ≫ e₁.hom)
          dsimp only [m, pushout.map]
          exact pushout.inr_desc _ _ _
        _ = c ≫ pushout.inr i' g' ≫ e₁.hom := Category.assoc _ _ _
        _ = c ≫ q' := by rw [h₁.inr_isoIsPushout_hom]
        _ = q ≫ d := hq.symm
  rw [← hd]
  infer_instance

/-- A map between two chosen pushout squares is a weak equivalence when the
second leg in each span is a cofibration and all three maps of span objects are
weak equivalences. -/
theorem IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
    {A B X P A' B' X' P' : C}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    [Cofibration g] [Cofibration g']
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence d :=
  IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
    sq.flip sq'.flip hg hi hq hp

end HomotopicalAlgebra
