-- Author: @toskua, Avocado
/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import MathlibExt.Algebra.Homology.GradedPairing
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairing
public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairingAssociativity

/-!
# Graded pairings on linear Hom-cochains

A chain map into a tensor product and a bilinear pairing of coefficient
modules induce a graded pairing on linear Hom-cochains. The descriptor,
degreewise map, and Leibniz law specialize the linear-Yoneda construction.
The module unit and associativity theorems use this same pairing.
-/

open CategoryTheory MonoidalCategory Opposite

noncomputable section

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]
variable {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
variable {M N P : ModuleCat.{u} R}
variable [HasTensor K₁ K₂]

@[simp]
private lemma moduleHom_comp_apply {A B C : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[simp]
private lemma moduleHom_add_apply {A B : ModuleCat.{u} R}
    (f g : A ⟶ B) (x : A) :
    (f + g).hom x = f.hom x + g.hom x := rfl

@[simp]
private lemma moduleHom_zsmul_apply {A B : ModuleCat.{u} R}
    (n : ℤ) (f : A ⟶ B) (x : A) :
    (n • f).hom x = n • f.hom x := rfl

@[simp]
private lemma moduleTensorHom_tmul {A B C D : ModuleCat.{u} R}
    (f : A ⟶ B) (g : C ⟶ D) (x : A) (y : C) :
    (f ⊗ₘ g).hom (x ⊗ₜ[R] y) = f.hom x ⊗ₜ[R] g.hom y := rfl

@[simp]
private lemma moduleLeftComp_apply {A B : ModuleCat.{u} R}
    (G : ModuleCat.{u} R) (f : A ⟶ B) (φ : B ⟶ G) :
    (ModuleCat.ofHom (Linear.leftComp R G f)).hom φ = f ≫ φ := rfl

private noncomputable def linearHomPairingDescOfEq
    (μ : M ⊗ N ⟶ P) (p q n : ℕ) (hpq : p + q = n)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    (tensorObj K₁ K₂).X n ⟶ P :=
  linearYonedaPairingDescOfEq (ModuleCat.{u} R) μ p q n hpq φ ψ

@[expose]
public noncomputable def linearHomPairingDesc
    (μ : M ⊗ N ⟶ P) (p q : ℕ)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    (tensorObj K₁ K₂).X (p + q) ⟶ P :=
  linearYonedaPairingDesc (ModuleCat.{u} R) μ p q φ ψ

@[reassoc (attr := simp)]
private lemma ιTensorObj_comp_linearHomPairingDescOfEq
    (μ : M ⊗ N ⟶ P) (p q n i j : ℕ) (hpq : p + q = n) (hij : i + j = n)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ i j n hij ≫
        linearHomPairingDescOfEq R μ p q n hpq φ ψ =
      if hi : i = p then
        by
          subst i
          have hsum : p + j = p + q := hij.trans hpq.symm
          have hj : j = q := Nat.add_left_cancel hsum
          subst j
          exact (φ ⊗ₘ ψ) ≫ μ
      else 0 := by
  exact ιTensorObj_comp_linearYonedaPairingDescOfEq
    (ModuleCat.{u} R) μ p q n i j hpq hij φ ψ

@[reassoc]
private lemma ιTensorObj_comp_linearHomPairingDescOfEq_of_eq
    (μ : M ⊗ N ⟶ P) (p q n i j : ℕ) (hpq : p + q = n) (hij : i + j = n)
    (hi : i = p) (hj : j = q)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ i j n hij ≫
        linearHomPairingDescOfEq R μ p q n hpq φ ψ =
      (((K₁.XIsoOfEq hi).hom ≫ φ) ⊗ₘ
        ((K₂.XIsoOfEq hj).hom ≫ ψ)) ≫ μ := by
  subst i
  subst j
  rw [ιTensorObj_comp_linearHomPairingDescOfEq]
  simp

private lemma XIsoOfEq_comp_linearHomPairingDesc
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : n = p + q)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    (K₃.XIsoOfEq h).hom ≫ Δ.f (p + q) ≫
        linearHomPairingDescOfEq R μ p q (p + q) rfl φ ψ =
      Δ.f n ≫ linearHomPairingDescOfEq R μ p q n h.symm φ ψ := by
  subst n
  rfl

/-- Degreewise pairing of linear Hom-cochains induced by a chain map into a tensor
product and a pairing of coefficient modules. -/
@[expose]
public noncomputable def linearHomCochainPair
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    ModuleCat.of R (K₁.X p ⟶ M) ⊗ ModuleCat.of R (K₂.X q ⟶ N) ⟶
      ModuleCat.of R (K₃.X (p + q) ⟶ P) :=
  linearYonedaCochainPair R (ModuleCat.{u} R) Δ μ p q

@[simp]
public lemma linearHomCochainPair_tmul
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M ⊗ N ⟶ P) (p q : ℕ)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    (linearHomCochainPair R Δ μ p q).hom (φ ⊗ₜ[R] ψ) =
      Δ.f (p + q) ≫ linearHomPairingDesc R μ p q φ ψ := by
  rw [linearHomCochainPair]
  rfl

@[simp]
lemma linearHomCochainComplex_d_apply
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R) (n : ℕ)
    (φ : K.X n ⟶ G) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj (op K)).d n (n + 1)).hom φ =
      K.d (n + 1) n ≫ φ := rfl

@[simp]
lemma linearHomCochainComplex_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R) (n : ℕ) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj (op K)).d n (n + 1) =
      ModuleCat.ofHom (Linear.leftComp R G (K.d (n + 1) n)) := rfl

@[simp]
lemma linearHomCochainComplex_XIsoOfEq_hom_apply
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R)
    {a b : ℕ} (h : a = b) (φ : K.X a ⟶ G) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj (op K)).XIsoOfEq h).hom.hom φ =
      (K.XIsoOfEq h.symm).hom ≫ φ := by
  subst b
  rfl

@[simp]
lemma linearHomCochainComplex_XIsoOfEq_hom
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (G : ModuleCat.{u} R)
    {a b : ℕ} (h : a = b) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) G).obj (op K)).XIsoOfEq h).hom =
      ModuleCat.ofHom (Linear.leftComp R G (K.XIsoOfEq h.symm).hom) := by
  subst b
  rfl

@[expose]
public noncomputable def linearHomCochainGradedPairing
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M ⊗ N ⟶ P) :
    CochainGradedPairing
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K₁))
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).obj (op K₂))
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).obj (op K₃)) :=
  linearYonedaCochainGradedPairing R (ModuleCat.{u} R) Δ μ

@[simp]
public lemma linearHomCochainGradedPairing_pair
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    (linearHomCochainGradedPairing R Δ μ).pair p q =
      linearHomCochainPair R Δ μ p q := by
  rfl

public theorem linearHomCochainPair_comp
    {L₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (f₃ : L₃ ⟶ K₃)
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    linearHomCochainPair R Δ μ p q ≫
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op).f (p + q) =
      linearHomCochainPair R (f₃ ≫ Δ) μ p q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ ψ
  rfl

public theorem linearHomCochainGradedPairing_pair_comp
    {L₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (f₃ : L₃ ⟶ K₃)
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    (linearHomCochainGradedPairing R Δ μ).pair p q ≫
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op).f (p + q) =
      (linearHomCochainGradedPairing R (f₃ ≫ Δ) μ).pair p q := by
  rw [linearHomCochainGradedPairing_pair,
    linearHomCochainGradedPairing_pair]
  exact linearHomCochainPair_comp R Δ f₃ μ p q

private lemma linearHomPairingDesc_naturality
    {L₁ L₂ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor L₁ L₂] (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂)
    (μ : M ⊗ N ⟶ P) (p q : ℕ)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    (tensorHom f₁ f₂).f (p + q) ≫
        linearHomPairingDesc R μ p q φ ψ =
      linearHomPairingDesc R μ p q (f₁.f p ≫ φ) (f₂.f q ≫ ψ) := by
  exact linearYonedaPairingDesc_naturality (ModuleCat.{u} R)
    f₁ f₂ μ p q φ ψ

private lemma monoidalTensorHom_f
    {L₁ L₂ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor L₁ L₂]
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (n : ℕ) :
    (f₁ ⊗ₘ f₂).f n = (tensorHom f₁ f₂).f n := rfl

public lemma linearHomCochainPair_naturality
    {L₁ L₂ L₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor L₁ L₂]
    (ΔK : K₃ ⟶ tensorObj K₁ K₂)
    (ΔL : L₃ ⟶ tensorObj L₁ L₂)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : L₃ ⟶ K₃)
    (hΔ : f₃ ≫ ΔK = ΔL ≫ (f₁ ⊗ₘ f₂))
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    linearHomCochainPair R ΔK μ p q ≫
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op).f (p + q) =
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).map f₁.op).f p ⊗ₘ
          ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).map f₂.op).f q) ≫
        linearHomCochainPair R ΔL μ p q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ ψ
  change f₃.f (p + q) ≫ ΔK.f (p + q) ≫
      linearHomPairingDesc R μ p q φ ψ =
    ΔL.f (p + q) ≫
      linearHomPairingDesc R μ p q (f₁.f p ≫ φ) (f₂.f q ≫ ψ)
  have hΔn : f₃.f (p + q) ≫ ΔK.f (p + q) =
      ΔL.f (p + q) ≫ (f₁ ⊗ₘ f₂).f (p + q) := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f => f.f (p + q)) hΔ
  rw [← Category.assoc, hΔn, monoidalTensorHom_f, Category.assoc,
    linearHomPairingDesc_naturality]

public lemma linearHomCochainGradedPairing_naturality
    {L₁ L₂ L₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor L₁ L₂]
    (ΔK : K₃ ⟶ tensorObj K₁ K₂)
    (ΔL : L₃ ⟶ tensorObj L₁ L₂)
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂) (f₃ : L₃ ⟶ K₃)
    (hΔ : f₃ ≫ ΔK = ΔL ≫ (f₁ ⊗ₘ f₂))
    (μ : M ⊗ N ⟶ P) (p q : ℕ) :
    (linearHomCochainGradedPairing R ΔK μ).pair p q ≫
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) P).map f₃.op).f (p + q) =
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).map f₁.op).f p ⊗ₘ
          ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) N).map f₂.op).f q) ≫
        (linearHomCochainGradedPairing R ΔL μ).pair p q := by
  rw [linearHomCochainGradedPairing_pair,
    linearHomCochainGradedPairing_pair]
  exact linearHomCochainPair_naturality R ΔK ΔL f₁ f₂ f₃ hΔ μ p q

public lemma linearHomCochainPair_coefficient_naturality
    {M' N' P' : ModuleCat.{u} R}
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (fM : M ⟶ M') (fN : N ⟶ N') (fP : P ⟶ P')
    (μ : M ⊗ N ⟶ P) (μ' : M' ⊗ N' ⟶ P')
    (hμ : (fM ⊗ₘ fN) ≫ μ' = μ ≫ fP)
    (p q : ℕ) :
    linearHomCochainPair R Δ μ p q ≫
        (((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fP).app
          (op K₃)).f (p + q) =
      ((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fM).app
          (op K₁)).f p ⊗ₘ
        (((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fN).app
          (op K₂)).f q) ≫
        linearHomCochainPair R Δ μ' p q := by
  exact linearYonedaCochainPair_coefficient_naturality R (ModuleCat.{u} R)
    Δ fM fN fP μ μ' hμ p q

public lemma linearHomCochainGradedPairing_coefficient_naturality
    {M' N' P' : ModuleCat.{u} R}
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (fM : M ⟶ M') (fN : N ⟶ N') (fP : P ⟶ P')
    (μ : M ⊗ N ⟶ P) (μ' : M' ⊗ N' ⟶ P')
    (hμ : (fM ⊗ₘ fN) ≫ μ' = μ ≫ fP)
    (p q : ℕ) :
    (linearHomCochainGradedPairing R Δ μ).pair p q ≫
        (((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fP).app
          (op K₃)).f (p + q) =
      ((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fM).app
          (op K₁)).f p ⊗ₘ
        (((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fN).app
          (op K₂)).f q) ≫
        (linearHomCochainGradedPairing R Δ μ').pair p q := by
  rw [linearHomCochainGradedPairing_pair,
    linearHomCochainGradedPairing_pair]
  exact linearHomCochainPair_coefficient_naturality R Δ fM fN fP μ μ' hμ p q

variable (K : ChainComplex (ModuleCat.{u} R) ℕ)

variable (A : ModuleCat.{u} R)

variable [ComonObj K] [MonObj A]

public noncomputable def linearHomCochainOne :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X 0 :=
  ComonObj.counit (X := K).f 0 ≫
    (singleObjXSelf (ComplexShape.down ℕ) 0
      (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)

@[simp]
public lemma linearHomCochain_d_one :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).d 0 1).hom
        (linearHomCochainOne R K A) = 0 := by
  change K.d 1 0 ≫ ComonObj.counit (X := K).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A) = 0
  have hd : K.d 1 0 ≫ ComonObj.counit (X := K).f 0 = 0 := by
    calc
      _ = ComonObj.counit (X := K).f 1 ≫
          (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).d 1 0 :=
        ((ComonObj.counit (X := K)).comm 1 0).symm
      _ = _ := by
        rw [show (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).d 1 0 = 0 by
          change ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj
            (𝟙_ (ModuleCat.{u} R))).d 1 0 = 0
          apply single_obj_d]
        simp
  rw [← Category.assoc, hd]
  simp

public noncomputable def linearHomCochainOneHom :
    𝟙_ (ModuleCat.{u} R) ⟶
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (linearHomCochainOne R K A))

@[simp]
public theorem linearHomCochainOneHom_apply_one :
    (linearHomCochainOneHom R K A).hom 1 =
      ComonObj.counit (X := K).f 0 ≫
        (singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A) := by
  change (1 : R) • linearHomCochainOne R K A = _
  rw [one_smul]
  rfl

@[simp]
public lemma linearHomCochainOneHom_d :
    linearHomCochainOneHom R K A ≫
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r • ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
    (op K)).d 0 1).hom (linearHomCochainOne R K A)) = 0
  rw [linearHomCochain_d_one]
  exact smul_zero r

public lemma linearHomCochainOne_coefficient_naturality {B : ModuleCat.{u} R} [MonObj B]
    (f : A ⟶ B) [IsMonHom f] :
    linearHomCochainOne R K A ≫ f = linearHomCochainOne R K B := by
  change ComonObj.counit (X := K).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A) ≫ f =
    ComonObj.counit (X := K).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := B)
  try simp only [Category.assoc]
  rw [IsMonHom.one_hom]

public lemma linearHomCochainOne_naturality (R : Type u) [CommRing R]
    (A : ModuleCat.{u} R) [MonObj A]
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) [ComonObj K] [ComonObj L]
    (f : K ⟶ L) [IsComonHom f] :
    f.f 0 ≫ linearHomCochainOne R L A = linearHomCochainOne R K A := by
  have h0 : (f ≫ ComonObj.counit (X := L)).f 0 =
      ComonObj.counit (X := K).f 0 := by
    rw [IsComonHom.hom_counit f]
  have h1 : f.f 0 ≫ ComonObj.counit (X := L).f 0 =
      ComonObj.counit (X := K).f 0 := by
    rwa [HomologicalComplex.comp_f] at h0
  change f.f 0 ≫ (ComonObj.counit (X := L).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) =
    ComonObj.counit (X := K).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)
  rw [← Category.assoc, h1]


private lemma linearHomCochainPair_one_left_apply
    (q : ℕ)
    (φ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).X q) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.zero_add q)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair 0 q).hom
          (linearHomCochainOne R K A ⊗ₜ[R] φ)) = φ := by
  change (K.X q ⟶ A) at φ
  erw [linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainComplex_XIsoOfEq_hom,
    ModuleCat.ofHom_apply, Linear.leftComp_apply]
  rw [linearHomCochainOne]
  unfold linearHomPairingDesc
  erw [XIsoOfEq_comp_linearHomPairingDesc R
    (ComonObj.comul (X := K)) (MonObj.mul (X := A)) 0 q q
    (Nat.zero_add q).symm
    (ComonObj.counit (X := K).f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ]
  have hdesc :
      linearHomPairingDescOfEq R (MonObj.mul (X := A)) 0 q q
          (Nat.zero_add q)
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ =
        (ComonObj.counit (X := K) ▷ K).f q ≫
          (λ_ K).hom.f q ≫ φ := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ιTensorObj_comp_linearHomPairingDescOfEq]
    change _ = ιTensorObj K K i j q h ≫
      (tensorHom (ComonObj.counit (X := K)) (𝟙 K)).f q ≫
        (λ_ K).hom.f q ≫ φ
    rw [ι_mapBifunctorMap_assoc]
    by_cases hi : i = 0
    · subst i
      have hj : j = q := by simpa using h
      subst j
      rw [show h = Nat.zero_add q from Subsingleton.elim _ _]
      simp only [dite_eq_left]
      have hunitor :
          ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K
                0 q q (Nat.zero_add q) ≫ (λ_ K).hom.f q =
            ((singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom ▷ K.X q) ≫
              (λ_ (K.X q)).hom := by
        rw [← cancel_epi ((singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).inv ▷ K.X q)]
        rw [← cancel_epi (λ_ (K.X q)).inv]
        slice_lhs 1 3 => erw [← leftUnitor'_inv]
        have hhom : (λ_ K).hom.f q = (leftUnitor' K).hom q := rfl
        rw [hhom]
        simp
      simp only [curriedTensor_obj_obj, curriedTensor_map_app, id_f,
        curriedTensor_obj_map, whiskerLeft_id, Category.id_comp]
      slice_rhs 2 3 => erw [hunitor]
      rw [MonoidalCategory.tensorHom_def_assoc]
      rw [MonoidalCategory.comp_whiskerRight_assoc,
        MonoidalCategory.comp_whiskerRight_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc, MonObj.one_mul]
      slice_lhs 3 4 => rw [MonoidalCategory.leftUnitor_naturality]
      rw [Category.assoc]
    · simp only [dite_eq_right hi]
      have hcounit : ComonObj.counit (X := K).f i = 0 := by
        apply (isZero_single_obj_X (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R)) i hi).eq_of_tgt
      rw [hcounit, Functor.map_zero]
      simp
  rw [hdesc]
  have hfinal : ComonObj.comul (X := K).f q ≫
      (ComonObj.counit (X := K) ▷ K).f q ≫
        (λ_ K).hom.f q ≫ φ = φ := by
    have hc := congrArg (fun f => f.f q) (ComonObj.counit_comul K)
    dsimp only [HomologicalComplex.comp_f] at hc
    slice_lhs 1 2 => rw [hc]
    simp
  exact hfinal


set_option backward.isDefEq.respectTransparency.types false in
public theorem linearHomCochainPair_one_left (q : ℕ) :
    (linearHomCochainOneHom R K A ⊗ₘ
        𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair 0 q ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.zero_add q)).hom =
    (λ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r φ
  change R at r
  change ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.zero_add q)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair 0 q).hom
          ((r • linearHomCochainOne R K A) ⊗ₜ[R] φ)) = r • φ
  rw [← TensorProduct.smul_tmul']
  rw [map_smul, map_smul]
  rw [linearHomCochainPair_one_left_apply]


private lemma linearHomCochainPair_one_right_apply
    (p : ℕ)
    (φ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).X p) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.add_zero p)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair p 0).hom
          (φ ⊗ₜ[R] linearHomCochainOne R K A)) = φ := by
  change (K.X p ⟶ A) at φ
  erw [linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul]
  rw [linearHomCochainOne]
  unfold linearHomPairingDesc
  change ComonObj.comul (X := K).f p ≫
      linearHomPairingDescOfEq R (MonObj.mul (X := A)) p 0 p rfl φ
        (ComonObj.counit (X := K).f 0 ≫
          (singleObjXSelf (ComplexShape.down ℕ) 0
            (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) = φ
  have hdesc :
      linearHomPairingDescOfEq R (MonObj.mul (X := A)) p 0 p
          (Nat.add_zero p) φ
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) =
        (K ◁ ComonObj.counit (X := K)).f p ≫
          (ρ_ K).hom.f p ≫ φ := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ιTensorObj_comp_linearHomPairingDescOfEq]
    change _ = ιTensorObj K K i j p h ≫
      (tensorHom (𝟙 K) (ComonObj.counit (X := K))).f p ≫
        (ρ_ K).hom.f p ≫ φ
    rw [ι_mapBifunctorMap_assoc]
    by_cases hi : i = p
    · subst i
      have hj : j = 0 := by
        change p + j = p at h
        omega
      subst j
      rw [show h = Nat.add_zero p from Subsingleton.elim _ _]
      simp only [dite_eq_left]
      have hunitor :
          ιTensorObj K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
                p 0 p (Nat.add_zero p) ≫ (ρ_ K).hom.f p =
            (K.X p ◁ (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom) ≫
              (ρ_ (K.X p)).hom := by
        rw [← cancel_epi (K.X p ◁
          (singleObjXSelf (ComplexShape.down ℕ) 0
            (𝟙_ (ModuleCat.{u} R))).inv)]
        rw [← cancel_epi (ρ_ (K.X p)).inv]
        slice_lhs 1 3 => erw [← rightUnitor'_inv]
        have hhom : (ρ_ K).hom.f p = (rightUnitor' K).hom p := rfl
        rw [hhom]
        simp
      simp only [curriedTensor_obj_obj, curriedTensor_map_app, id_f,
        curriedTensor_obj_map, id_whiskerRight, Category.id_comp]
      slice_rhs 2 3 => erw [hunitor]
      rw [MonoidalCategory.tensorHom_def_assoc]
      rw [MonoidalCategory.whiskerLeft_comp_assoc,
        MonoidalCategory.whiskerLeft_comp_assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc,
        ← MonoidalCategory.whisker_exchange_assoc]
      rw [MonObj.mul_one]
      slice_lhs 3 4 => rw [MonoidalCategory.rightUnitor_naturality]
      rw [Category.assoc]
    · have hj : j ≠ 0 := by
        intro hj
        subst j
        apply hi
        simpa using h
      simp only [dite_eq_right hi]
      have hcounit : ComonObj.counit (X := K).f j = 0 := by
        apply (isZero_single_obj_X (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R)) j hj).eq_of_tgt
      rw [hcounit, Functor.map_zero]
      simp
  rw [hdesc]
  have hfinal : ComonObj.comul (X := K).f p ≫
      (K ◁ ComonObj.counit (X := K)).f p ≫
        (ρ_ K).hom.f p ≫ φ = φ := by
    have hc := congrArg (fun f => f.f p) (ComonObj.comul_counit K)
    dsimp only [HomologicalComplex.comp_f] at hc
    slice_lhs 1 2 => rw [hc]
    simp
  exact hfinal

private lemma linearHomCochainPair_one_right_smul
    (p : ℕ)
    (φ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).X p) (r : R) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.add_zero p)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair p 0).hom
          (φ ⊗ₜ[R] (r • linearHomCochainOne R K A))) = r • φ := by
  rw [TensorProduct.tmul_smul, map_smul, map_smul,
    linearHomCochainPair_one_right_apply R K A p φ]


set_option backward.isDefEq.respectTransparency.types false in
public theorem linearHomCochainPair_one_right (p : ℕ) :
    (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p) ⊗ₘ
        linearHomCochainOneHom R K A) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair p 0 ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.add_zero p)).hom =
    (ρ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ r
  change R at r
  change ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.add_zero p)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair p 0).hom
          (φ ⊗ₜ[R] (r • linearHomCochainOne R K A))) = r • φ
  exact linearHomCochainPair_one_right_smul R K A p φ r

set_option backward.isDefEq.respectTransparency.types false in
public theorem linearHomCochainPair_assoc (p q r : ℕ) :
    (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair p q ⊗ₘ
      𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X r)) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair (p + q) r ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.add_assoc p q r)).hom) =
    (α_
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p)
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X r)).hom ≫
      (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p) ⊗ₘ
        (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair q r) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair p (q + r) := by
  have hΔ : 𝟙 K ≫ ComonObj.comul (X := K) ≫
      tensorHom (ComonObj.comul (X := K)) (𝟙 K) ≫
        (HomologicalComplex.associator K K K).hom =
      ComonObj.comul (X := K) ≫
        tensorHom (𝟙 K) (ComonObj.comul (X := K)) := by
    apply Hom.ext
    funext n
    have hn := congrArg (fun f => f.f n) (ComonObj.comul_assoc K).symm
    dsimp only [HomologicalComplex.comp_f] at hn
    change ComonObj.comul (X := K).f n ≫
        (tensorHom (ComonObj.comul (X := K)) (𝟙 K)).f n ≫
          (HomologicalComplex.associator K K K).hom.f n =
      ComonObj.comul (X := K).f n ≫
        (tensorHom (𝟙 K) (ComonObj.comul (X := K))).f n at hn
    simpa only [HomologicalComplex.comp_f, id_f, Category.id_comp] using hn
  have hμ : (MonObj.mul (X := A) ▷ A) ≫ MonObj.mul (X := A) ≫ 𝟙 A =
      (α_ A A A).hom ≫ (A ◁ MonObj.mul (X := A)) ≫ MonObj.mul (X := A) := by
    simpa only [Category.comp_id] using MonObj.mul_assoc A
  have hcompare : linearYonedaCochainComparison R (ModuleCat.{u} R)
      (𝟙 K) (𝟙 A) = 𝟙 _ := by
    simp [linearYonedaCochainComparison]
    rfl
  simpa only [linearHomCochainGradedPairing, hcompare, id_f,
    Category.id_comp, Category.comp_id] using
    linearYonedaCochainPair_associativity_of_diagrams R (ModuleCat.{u} R)
      (ComonObj.comul (X := K)) (ComonObj.comul (X := K))
      (ComonObj.comul (X := K)) (ComonObj.comul (X := K)) (𝟙 K)
      (MonObj.mul (X := A)) (MonObj.mul (X := A))
      (MonObj.mul (X := A)) (MonObj.mul (X := A)) (𝟙 A) hΔ hμ p q r

/-- The linear-Hom pairing descriptor is supported only in its specified
bidegree, with the expected tensor pairing there. -/
@[reassoc]
public lemma ιTensorObj_comp_linearHomPairingDesc
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M N P : ModuleCat.{u} R}
    (μ : M ⊗ N ⟶ P) (p q i j : ℕ) (hij : i + j = p + q)
    (φ : K₁.X p ⟶ M) (ψ : K₂.X q ⟶ N) :
    ιTensorObj K₁ K₂ i j (p + q) hij ≫
        linearHomPairingDesc R μ p q φ ψ =
      if hi : i = p then
        by
          subst i
          have hj : j = q := Nat.add_left_cancel hij
          subst j
          exact (φ ⊗ₘ ψ) ≫ μ
      else 0 := by
  unfold linearHomPairingDesc linearYonedaPairingDesc
  rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel hij
    subst j
    simp
  · simp [hi]

/-- Postcomposing a pairing descriptor with left-unitor coefficients is the
same as using the postcomposition as its second input. -/
public theorem linearHomPairingDesc_leftUnitor_comp
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ}
    {N : ModuleCat.{u} R} [K₁.HasTensor K₂]
    (p q : ℕ) (φ : K₁.X p ⟶ 𝟙_ (ModuleCat.{u} R))
    (f : K₂.X q ⟶ N) :
    linearHomPairingDesc R (λ_ (K₂.X q)).hom p q φ (𝟙 _) ≫ f =
      linearHomPairingDesc R (λ_ N).hom p q φ f := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_comp_linearHomPairingDesc_assoc,
    ιTensorObj_comp_linearHomPairingDesc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [dite_eq_left]
    rw [Category.assoc, ← MonoidalCategory.leftUnitor_naturality]
    change (((φ ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ f)) ≫ (λ_ N).hom) = _
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  · simp [hi]

end HomologicalComplex
