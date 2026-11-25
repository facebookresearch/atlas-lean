/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
public import MathlibExt.Algebra.Homology.ChainGradedPairing
public import MathlibExt.Algebra.Homology.CochainChainGradedPairing
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]
variable {K₁ K₂ K₃ L : ChainComplex (ModuleCat.{u} R) ℕ}
variable {A : ModuleCat.{u} R}
variable [HasTensor K₁ K₂]

/-- Descend a linear Hom-cochain against the second tensor factor via `ρ`,
keeping only the `(p, q)`-component. -/
public noncomputable def linearHomCochainChainPairDesc
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ : K₁.X p ⟶ A) :
    (tensorObj K₁ K₂).X (p + q) ⟶ L.X q :=
  mapBifunctorDesc (fun i j h =>
    if hi : i = p then
      by
        subst i
        have hj : j = q := Nat.add_left_cancel h
        subst j
        exact (φ ⊗ₘ 𝟙 _) ≫ ρ q
    else 0)

/-- The cochain-chain descriptor is supported only in its specified bidegree,
with the expected tensor action there. -/
@[reassoc]
public lemma ιTensorObj_comp_linearHomCochainChainPairDesc
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q i j : ℕ) (hij : i + j = p + q)
    (φ : K₁.X p ⟶ A) :
    ιTensorObj K₁ K₂ i j (p + q) hij ≫
        linearHomCochainChainPairDesc R ρ p q φ =
      if hi : i = p then
        by
          subst i
          have hj : j = q := Nat.add_left_cancel hij
          subst j
          exact (φ ⊗ₘ 𝟙 _) ≫ ρ q
      else 0 := by
  unfold linearHomCochainChainPairDesc
  rw [ι_mapBifunctorDesc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel hij
    subst j
    simp
  · simp [hi]

private lemma linearHomCochainChainPairDesc_add
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ₁ φ₂ : K₁.X p ⟶ A) :
    linearHomCochainChainPairDesc R ρ p q (φ₁ + φ₂) =
      linearHomCochainChainPairDesc R ρ p q φ₁ +
        linearHomCochainChainPairDesc R ρ p q φ₂ := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearHomCochainChainPairDesc
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [ι_mapBifunctorDesc, dite_eq_left, Preadditive.comp_add]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp
  · simp [hi, Preadditive.comp_add]

private lemma linearHomCochainChainPairDesc_smul
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ) (r : R)
    (φ : K₁.X p ⟶ A) :
    linearHomCochainChainPairDesc R ρ p q (r • φ) =
      r • linearHomCochainChainPairDesc R ρ p q φ := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearHomCochainChainPairDesc
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [ι_mapBifunctorDesc, dite_eq_left, Linear.comp_smul]
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp
  · simp [hi, Linear.comp_smul]

/-- Pair a linear Hom-cochain with a chain after a chain diagonal. -/
public noncomputable def linearHomCochainChainPair
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ) :
    ModuleCat.of R (K₁.X p ⟶ A) ⊗ K₃.X (p + q) ⟶ L.X q :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun φ x =>
      (Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q φ).hom x)
    (fun φ₁ φ₂ x => by
      rw [linearHomCochainChainPairDesc_add, Preadditive.comp_add]
      rfl)
    (fun r φ x => by
      rw [linearHomCochainChainPairDesc_smul, Linear.comp_smul]
      rfl)
    (fun φ x₁ x₂ => map_add _ _ _)
    (fun r φ x => map_smul _ _ _)

/-- Evaluate the linear cochain-chain pairing on a pure tensor through the descended pairing. -/
@[simp]
public lemma linearHomCochainChainPair_tmul
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ : K₁.X p ⟶ A) (x : K₃.X (p + q)) :
    (linearHomCochainChainPair R Δ ρ p q).hom (φ ⊗ₜ[R] x) =
      (Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q φ).hom x := by
  rw [linearHomCochainChainPair]
  rfl

@[simp]
private lemma moduleHom_comp_apply {U V W : ModuleCat.{u} R}
    (f : U ⟶ V) (g : V ⟶ W) (x : U) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp]
private lemma moduleHom_sub_apply {U V : ModuleCat.{u} R}
    (f g : U ⟶ V) (x : U) :
    (f - g).hom x = f.hom x - g.hom x := rfl

@[simp]
private lemma moduleHom_zsmul_apply {U V : ModuleCat.{u} R}
    (n : ℤ) (f : U ⟶ V) (x : U) :
    (n • f).hom x = n • f.hom x := rfl

@[simp]
private lemma linearHomCochainComplex_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R) (n : ℕ) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj
      (op K)).d n (n + 1) =
      ModuleCat.ofHom (Linear.leftComp R G (K.d (n + 1) n)) := rfl

/-- Restrict a chain graded pairing with singleton degree-zero source to its degree-`q` action. -/
public noncomputable def chainGradedPairingDegreeZeroAction
    (B : ChainGradedPairing
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂ L)
    (q : ℕ) : A ⊗ K₂.X q ⟶ L.X q :=
  ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K₂.X q) ≫
    ιTensorObj ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂
      0 q q (Nat.zero_add q) ≫ B.f q

/-- Rewrite the degree-zero action through the graded pair and the `0 + q = q` equality iso. -/
public theorem chainGradedPairingDegreeZeroAction_normalization
    (B : ChainGradedPairing
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂ L)
    (q : ℕ) :
    chainGradedPairingDegreeZeroAction R B q =
      ((singleObjXSelf (ComplexShape.down ℕ) 0 A).inv ▷ K₂.X q) ≫
        B.pair 0 q ≫ (L.XIsoOfEq (Nat.zero_add q)).hom := by
  unfold chainGradedPairingDegreeZeroAction
  rw [ChainGradedPairing.pair]
  simp only [Category.assoc]
  rw [XIsoOfEq_hom_naturality]
  have hi (n : ℕ) (e : 0 + q = n) :
      ιTensorObj ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂
          0 q (0 + q) rfl ≫
        ((tensorObj ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂).XIsoOfEq e).hom =
      ιTensorObj ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂
        0 q n e := by
    subst n
    simp only [XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
  slice_rhs 2 3 =>
    rw [hi q (Nat.zero_add q)]

private lemma chainGradedPairingDegreeZeroAction_d
    (B : ChainGradedPairing
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂ L)
    (q : ℕ) :
    chainGradedPairingDegreeZeroAction R B (q + 1) ≫ L.d (q + 1) q =
      (𝟙 A ⊗ₘ K₂.d (q + 1) q) ≫
        chainGradedPairingDegreeZeroAction R B q := by
  unfold chainGradedPairingDegreeZeroAction
  simp only [Category.assoc]
  rw [B.comm]
  slice_lhs 2 3 => rw [ιTensorObj_comp_d_down_nat]
  simp only [dite_eq_left True.intro, dite_eq_right (Nat.succ_ne_zero q), Nat.add_one_sub_one,
    pow_zero, one_smul, zero_add]
  slice_lhs 1 2 =>
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom]
  slice_rhs 1 2 =>
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]

private noncomputable def linearHomCochainChainPairComponent
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q n : ℕ) (hpq : p + q = n)
    (φ : K₁.X p ⟶ A) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i, j) = n) : K₁.X i ⊗ K₂.X j ⟶ L.X q :=
    if hi : i = p then
      by
        subst i
        have hsum : p + j = p + q := hij.trans hpq.symm
        have hj : j = q := Nat.add_left_cancel hsum
        subst j
        exact (φ ⊗ₘ 𝟙 _) ≫ ρ q
    else 0

private noncomputable def linearHomCochainChainPairDescOfEq
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q n : ℕ) (h : p + q = n)
    (φ : K₁.X p ⟶ A) :
    (tensorObj K₁ K₂).X n ⟶ L.X q :=
  mapBifunctorDesc (linearHomCochainChainPairComponent R ρ p q n h φ)

@[reassoc (attr := simp)]
private lemma ιTensorObj_comp_linearHomCochainChainPairDescOfEq
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (p q n i j : ℕ) (hpq : p + q = n) (hij : i + j = n)
    (φ : K₁.X p ⟶ A) :
    ιTensorObj K₁ K₂ i j n hij ≫
        linearHomCochainChainPairDescOfEq R ρ p q n hpq φ =
      linearHomCochainChainPairComponent R ρ p q n hpq φ i j hij := by
  unfold linearHomCochainChainPairDescOfEq
  apply ι_mapBifunctorDesc

private lemma tensor_d_comp_linearHomCochainChainPairDesc
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (hρ : ∀ q, ρ (q + 1) ≫ L.d (q + 1) q =
      (𝟙 A ⊗ₘ K₂.d (q + 1) q) ≫ ρ q)
    (p q n : ℕ) (hn : n = p + q + 1) (φ : K₁.X p ⟶ A) :
    (tensorObj K₁ K₂).d n (p + q) ≫
        linearHomCochainChainPairDescOfEq R ρ p q (p + q) rfl φ =
      linearHomCochainChainPairDescOfEq R ρ (p + 1) q n
          (by omega) (K₁.d (p + 1) p ≫ φ) +
        ((-1 : ℤ) ^ p) •
          (linearHomCochainChainPairDescOfEq R ρ p (q + 1) n
              (by omega) φ ≫
            L.d (q + 1) q) := by
  subst n
  apply mapBifunctor.hom_ext
  intro i j h
  change i + j = p + q + 1 at h
  rw [← Category.assoc, ιTensorObj_comp_d_down_nat K₁ K₂ i j (p + q) (by omega),
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_zsmul]
  by_cases hi_left : i = p + 1
  · subst i
    have hj : j = q := by omega
    subst j
    simp only [dite_eq_right (by omega : p + 1 ≠ 0), Nat.add_one_sub_one,
      tensorHom_id]
    rw [Category.assoc, ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
    simp only [linearHomCochainChainPairComponent]
    simp only [dite_eq_left True.intro]
    rw [ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
    simp only [linearHomCochainChainPairComponent]
    simp only [dite_eq_left True.intro]
    rw [ιTensorObj_comp_linearHomCochainChainPairDescOfEq_assoc]
    simp only [linearHomCochainChainPairComponent]
    simp only [dite_eq_right (by omega : p + 1 ≠ p)]
    have hmain :
        (K₁.d (p + 1) p ▷ K₂.X q) ≫
            (φ ⊗ₘ 𝟙 (K₂.X q)) ≫ ρ q =
          ((K₁.d (p + 1) p ≫ φ) ⊗ₘ 𝟙 (K₂.X q)) ≫ ρ q := by
      slice_lhs 1 2 =>
        rw [← MonoidalCategory.tensorHom_id,
          MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    rw [hmain]
    simp only [smul_zero, Limits.zero_comp, add_zero]
    rw [add_eq_left]
    by_cases hq : q = 0
    · simp [hq]
    · rw [dite_eq_right hq, Preadditive.zsmul_comp, Category.assoc,
        ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
      simp [linearHomCochainChainPairComponent]
  · by_cases hi_right : i = p
    · subst i
      have hj : j = q + 1 := by omega
      subst j
      simp only [dite_eq_right (by omega : q + 1 ≠ 0), Nat.add_one_sub_one,
        id_tensorHom]
      rw [Preadditive.zsmul_comp, Category.assoc,
        ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
      simp only [linearHomCochainChainPairComponent]
      simp only [dite_eq_left True.intro]
      rw [ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
      simp only [linearHomCochainChainPairComponent]
      simp only [dite_eq_right (by omega : p ≠ p + 1)]
      rw [ιTensorObj_comp_linearHomCochainChainPairDescOfEq_assoc]
      simp only [linearHomCochainChainPairComponent]
      simp only [dite_eq_left True.intro]
      have hmain :
          (K₁.X p ◁ K₂.d (q + 1) q) ≫
              (φ ⊗ₘ 𝟙 (K₂.X q)) ≫ ρ q =
            (φ ⊗ₘ 𝟙 (K₂.X (q + 1))) ≫ ρ (q + 1) ≫
              L.d (q + 1) q := by
        rw [hρ]
        slice_lhs 1 2 =>
          rw [← MonoidalCategory.id_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom]
        slice_rhs 1 2 =>
          rw [MonoidalCategory.tensorHom_comp_tensorHom]
        simp
      rw [hmain]
      simp only [zero_add, Category.assoc]
      rw [add_eq_right]
      by_cases hp : p = 0
      · simp [hp]
      · have hp_pred : p - 1 ≠ p := by omega
        rw [dite_eq_right hp, Category.assoc,
          ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
        simp [linearHomCochainChainPairComponent, hp_pred]
    · by_cases hi_zero : i = 0
      · subst i
        have hp : p ≠ 0 := by omega
        have hp' : 0 ≠ p := by omega
        have hj_zero : j ≠ 0 := by omega
        rw [dite_eq_left rfl, dite_eq_right hj_zero, Limits.zero_comp, zero_add]
        simp [linearHomCochainChainPairComponent, hp, hp']
      · have hi_pred : i - 1 ≠ p := by
          intro hip
          omega
        by_cases hj_zero : j = 0
        · rw [dite_eq_right hi_zero, dite_eq_left hj_zero, Limits.zero_comp, add_zero]
          simp [linearHomCochainChainPairComponent, hi_pred, hi_left, hi_right]
        · rw [dite_eq_right hi_zero, dite_eq_right hj_zero]
          simp [linearHomCochainChainPairComponent, hi_pred, hi_left, hi_right]

private lemma linearHomCochainChainPairDesc_eq_ofEq
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ : K₁.X p ⟶ A) :
    linearHomCochainChainPairDesc R ρ p q φ =
      linearHomCochainChainPairDescOfEq R ρ p q (p + q) rfl φ := by
  apply mapBifunctor.hom_ext
  intro i j h
  change i + j = p + q at h
  unfold linearHomCochainChainPairDesc
  rw [ι_mapBifunctorDesc,
    ιTensorObj_comp_linearHomCochainChainPairDescOfEq]
  unfold linearHomCochainChainPairComponent
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    simp only [dite_eq_left True.intro]
  · simp only [dite_eq_right hi]

private lemma XIsoOfEq_comp_linearHomCochainChainPairDesc
    (delta : K₃ ⟶ tensorObj K₁ K₂)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (p q n : ℕ) (h : n = p + q) (φ : K₁.X p ⟶ A) :
    (K₃.XIsoOfEq h).hom ≫ delta.f (p + q) ≫
        linearHomCochainChainPairDesc R ρ p q φ =
      delta.f n ≫
        linearHomCochainChainPairDescOfEq R ρ p q n h.symm φ := by
  subst n
  simp only [XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rw [linearHomCochainChainPairDesc_eq_ofEq]

private lemma linearHomCochainChainPairDesc_boundary
    (delta : K₃ ⟶ tensorObj K₁ K₂)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (hρ : ∀ q, ρ (q + 1) ≫ L.d (q + 1) q =
      (𝟙 A ⊗ₘ K₂.d (q + 1) q) ≫ ρ q)
    (p q : ℕ) (φ : K₁.X p ⟶ A) :
    delta.f (p + (q + 1)) ≫
        linearHomCochainChainPairDesc R ρ p (q + 1) φ ≫
          L.d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        ((K₃.d (p + (q + 1)) (p + q) ≫ delta.f (p + q) ≫
            linearHomCochainChainPairDesc R ρ p q φ) -
          ((K₃.XIsoOfEq
              (show (p + 1) + q = p + (q + 1) by omega)).inv ≫
            delta.f ((p + 1) + q) ≫
            linearHomCochainChainPairDesc R ρ (p + 1) q
              (K₁.d (p + 1) p ≫ φ))) := by
  have hTensor := tensor_d_comp_linearHomCochainChainPairDesc R ρ hρ p q
    (p + (q + 1)) (by omega) φ
  have hY :
      K₃.d (p + (q + 1)) (p + q) ≫ delta.f (p + q) ≫
          linearHomCochainChainPairDesc R ρ p q φ =
        (K₃.XIsoOfEq
            (show (p + 1) + q = p + (q + 1) by omega)).inv ≫
              delta.f ((p + 1) + q) ≫
              linearHomCochainChainPairDesc R ρ (p + 1) q
                (K₁.d (p + 1) p ≫ φ) +
          ((-1 : ℤ) ^ p) •
            (delta.f (p + (q + 1)) ≫
              linearHomCochainChainPairDesc R ρ p (q + 1) φ ≫
                L.d (q + 1) q) := by
    rw [linearHomCochainChainPairDesc_eq_ofEq R ρ p q φ,
      linearHomCochainChainPairDesc_eq_ofEq R ρ (p + 1) q
        (K₁.d (p + 1) p ≫ φ),
      linearHomCochainChainPairDesc_eq_ofEq R ρ p (q + 1) φ]
    rw [← Category.assoc, ← delta.comm]
    rw [Category.assoc, hTensor, Preadditive.comp_add,
      Preadditive.comp_zsmul]
    rw [← XIsoOfEq_comp_linearHomCochainChainPairDesc R]
    · rw [linearHomCochainChainPairDesc_eq_ofEq]
      congr 2
    · omega
  rw [hY]
  simp only [add_sub_cancel_left, smul_smul]
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  rw [hs, one_smul]

/-- The signed degree-lowering pairing induced by a chain diagonal and a
degree-zero chain action. -/
public noncomputable def linearHomCochainChainGradedPairing
    (delta : K₃ ⟶ tensorObj K₁ K₂)
    (B : ChainGradedPairing
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂ L) :
    CochainChainGradedPairing
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K₁))
      K₃ L where
  pair := linearHomCochainChainPair R delta
    (chainGradedPairingDegreeZeroAction R B)
  boundary := by
    intro p q
    simp only [linearHomCochainComplex_d,
      linearHomCochainComplexFunctor_obj_X]
    change linearHomCochainChainPair R delta
        (chainGradedPairingDegreeZeroAction R B) p (q + 1) ≫
          L.d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (((𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ
            K₃.d (p + (q + 1)) (p + q)) ≫
              linearHomCochainChainPair R delta
                (chainGradedPairingDegreeZeroAction R B) p q) -
          ((ModuleCat.ofHom (Linear.leftComp R A (K₁.d (p + 1) p)) ⊗ₘ
              (K₃.XIsoOfEq
                (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
            linearHomCochainChainPair R delta
              (chainGradedPairingDegreeZeroAction R B) (p + 1) q))
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro phi x
    change (K₁.X p ⟶ A) at phi
    change K₃.X (p + (q + 1)) at x
    change (L.d (q + 1) q).hom
        ((linearHomCochainChainPair R delta
          (chainGradedPairingDegreeZeroAction R B) p (q + 1)).hom
            (phi ⊗ₜ[R] x)) = _
    rw [linearHomCochainChainPair_tmul]
    simp only [moduleHom_zsmul_apply, moduleHom_sub_apply,
      moduleHom_comp_apply]
    change (delta.f (p + (q + 1)) ≫
        linearHomCochainChainPairDesc R
          (chainGradedPairingDegreeZeroAction R B) p (q + 1) phi ≫
          L.d (q + 1) q).hom x =
      (((-1 : ℤ) ^ p) •
        ((K₃.d (p + (q + 1)) (p + q) ≫ delta.f (p + q) ≫
            linearHomCochainChainPairDesc R
              (chainGradedPairingDegreeZeroAction R B) p q phi) -
          ((K₃.XIsoOfEq
              (show (p + 1) + q = p + (q + 1) by omega)).inv ≫
            delta.f ((p + 1) + q) ≫
            linearHomCochainChainPairDesc R
              (chainGradedPairingDegreeZeroAction R B) (p + 1) q
                (K₁.d (p + 1) p ≫ phi)))).hom x
    exact congrArg (fun f => f.hom x)
      (linearHomCochainChainPairDesc_boundary R delta
        (chainGradedPairingDegreeZeroAction R B)
        (chainGradedPairingDegreeZeroAction_d R B) p q phi)

/-- Identify the graded pairing's `(p, q)`-component with the linear cochain-chain pairing. -/
@[simp]
public theorem linearHomCochainChainGradedPairing_pair
    (delta : K₃ ⟶ tensorObj K₁ K₂)
    (B : ChainGradedPairing
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) K₂ L)
    (p q : ℕ) :
    (linearHomCochainChainGradedPairing R delta B).pair p q =
      linearHomCochainChainPair R delta
        (chainGradedPairingDegreeZeroAction R B) p q := rfl

end HomologicalComplex

end
