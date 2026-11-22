/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells

/-!
# Gluing along h-cofibrations

In a left proper model category, a commutative map between pushout squares
along h-cofibrations induces a weak equivalence on the pushout objects when
its three span maps are weak equivalences. The proof factors the remaining
leg as a cofibration followed by a trivial fibration and uses weak-equivalence
preservation under cobase change along h-cofibrations. The span endpoints are
arbitrary, and conventional h-monoidality supplies the left-properness hypothesis.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.HCofibrationGluing
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]

omit [IsLeftProper C] in
/-- The original definition of h-cofibration preserves weak maps under every cobase change. -/
theorem weakEquivalence_of_pushout_hCof
    {A B X Y : C} {i : A ⟶ B} {f : A ⟶ X} {p : B ⟶ Y} {q : X ⟶ Y}
    (sq : IsPushout i f p q) (hi : hCofibrations C i) [WeakEquivalence f] :
    WeakEquivalence p := by
  apply (weakEquivalence_iff _).mpr
  exact (hi A B (𝟙 A) i (𝟙 B) IsPushout.of_id_fst).of_isPushout sq
    (mem_weakEquivalences f)

private theorem weakEquivalence_pushoutMap_of_hCof
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : C}
    {u₀ : P₀ ⟶ Q₀} {v₀ : P₀ ⟶ R₀}
    {u₁ : P₁ ⟶ Q₁} {v₁ : P₁ ⟶ R₁}
    {wP : P₀ ⟶ P₁} {wQ : Q₀ ⟶ Q₁} {wR : R₀ ⟶ R₁}
    (hu : u₀ ≫ wQ = wP ≫ u₁) (hv : v₀ ≫ wR = wP ≫ v₁)
    (hu₀ : hCofibrations C u₀) (hu₁ : hCofibrations C u₁)
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
  have hLP : hCofibrations C lP := by
    dsimp only [lP]
    exact (hCofibrations C).of_isPushout (IsPushout.of_hasPushout u₀ wP).flip hu₀
  let _ : WeakEquivalence lQ :=
    weakEquivalence_of_pushout_hCof (IsPushout.of_hasPushout u₀ wP) hu₀
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
  have hAP : hCofibrations C (pushout.inr lP k) :=
    (hCofibrations C).of_isPushout (IsPushout.of_hasPushout lP k).flip hLP
  let _ : WeakEquivalence a := weakEquivalence_of_pushout_hCof haSq hAP
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
  have hBP : hCofibrations C (pushout.inr u₁ k) :=
    (hCofibrations C).of_isPushout (IsPushout.of_hasPushout u₁ k).flip hu₁
  let _ : WeakEquivalence b := weakEquivalence_of_pushout_hCof hbSq hBP
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
  have hA₀P : hCofibrations C (pushout.inr u₀ v₀) :=
    (hCofibrations C).of_isPushout (IsPushout.of_hasPushout u₀ v₀).flip hu₀
  let _ : WeakEquivalence a₀ := weakEquivalence_of_pushout_hCof ha₀Sq hA₀P
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

theorem weakEquivalence_map_of_isPushouts_of_hCof
    {A B X P A' B' X' P' : C}
    {i : A ⟶ B} {g : A ⟶ X} {p : B ⟶ P} {q : X ⟶ P}
    {i' : A' ⟶ B'} {g' : A' ⟶ X'} {p' : B' ⟶ P'} {q' : X' ⟶ P'}
    (sq : IsPushout i g p q) (sq' : IsPushout i' g' p' q')
    {a : A ⟶ A'} {b : B ⟶ B'} {c : X ⟶ X'} {d : P ⟶ P'}
    (hi : i ≫ b = a ≫ i') (hg : g ≫ c = a ≫ g')
    (hp : p ≫ d = b ≫ p') (hq : q ≫ d = c ≫ q')
    (hiH : hCofibrations C i) (hiH' : hCofibrations C i')
    [WeakEquivalence a] [WeakEquivalence b] [WeakEquivalence c] :
    WeakEquivalence d := by
  let h₀ := IsPushout.of_hasPushout i g
  let h₁ := IsPushout.of_hasPushout i' g'
  let m : pushout i g ⟶ pushout i' g' :=
    pushout.map i g i' g' b c a hi hg
  let _ : WeakEquivalence m := weakEquivalence_pushoutMap_of_hCof hi hg hiH hiH'
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


end HomotopicalAlgebra.HCofibrationGluing
