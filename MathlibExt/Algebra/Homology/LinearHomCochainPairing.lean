/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Avocado
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
# Pairings of module Hom cochains

Let R be a commutative ring, K₁, K₂, K₃ nonnegative chain complexes of
R-modules, and M, N, P coefficient modules, all with carriers in universe u.
A chain map Δ : K₃ → K₁ ⊗ K₂ and an R-linear map μ : M ⊗[R] N → P induce
Hom_R(K₁; M)^p ⊗[R] Hom_R(K₂; N)^q → Hom_R(K₃; P)^(p+q).

For cochains φ and ψ, the resulting map is Δ_(p+q) followed by the tensor
descriptor which equals μ ∘ (φ ⊗ ψ) on the (p, q) summand and is zero on
the other summands. The cochain differential is φ ↦ φ ∘ d_K, and the
pairing satisfies d(φ ∪ ψ) = dφ ∪ ψ + (-1)^p φ ∪ dψ.
The indicated total tensor product K₁ ⊗ K₂ is assumed to exist.
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

/-- Let R be a commutative ring, K₁, K₂, K₃ nonnegative chain complexes of
R-modules with K₁ ⊗ K₂ defined, Δ : K₃ → K₁ ⊗ K₂ a chain map, and
μ : M ⊗[R] N → P an R-linear coefficient pairing. For p, q ∈ ℕ, this is
the R-linear map Hom_R(K₁,p, M) ⊗[R] Hom_R(K₂,q, N) →
Hom_R(K₃,p+q, P). It sends φ ⊗ ψ to Δ_(p+q) followed by the descriptor
μ ∘ (φ ⊗ ψ) on the (p, q) summand and zero on every other summand. -/
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
  dsimp only [linearHomCochainComplexFunctor_obj_X] at φ ⊢
  have hcoord : (λ_ K).inv.f q = (leftUnitor' K).inv q := rfl
  have hinv : (λ_ K).inv.f q =
      (λ_ (K.X q)).inv ≫
        ((singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).inv ▷ K.X q) ≫
            ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K
              0 q q (Nat.zero_add q) := by
    rw [hcoord, leftUnitor'_inv]
    rfl
  have hcancel : (λ_ K).hom.f q ≫ (λ_ K).inv.f q =
      𝟙 (((𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ⊗ K).X q) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg
        (fun f : (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ⊗ K ⟶
            (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ⊗ K => f.f q)
        (λ_ K).hom_inv_id
  have hunitor :
      ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K
          0 q q (Nat.zero_add q) ≫ (λ_ K).hom.f q =
        ((singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).hom ▷ K.X q) ≫ (λ_ (K.X q)).hom := by
    apply (cancel_mono ((λ_ K).inv.f q)).mp
    calc
      _ = ιTensorObj (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) K
          0 q q (Nat.zero_add q) := by
        rw [Category.assoc, hcancel]
        exact Category.comp_id _
      _ = _ := by
        rw [hinv]
        simp only [Category.assoc, Iso.hom_inv_id_assoc,
          MonoidalCategory.hom_inv_whiskerRight_assoc]
  have hunitorPost := congrArg
    (fun f : (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).X 0 ⊗ K.X q ⟶ K.X q =>
      f ≫ φ) hunitor
  simp only [Category.assoc] at hunitorPost
  have hwhisk : (ComonObj.counit (X := K) ▷ K).f q =
      (tensorHom (ComonObj.counit (X := K)) (𝟙 K)).f q := rfl
  have hdesc :
      linearYonedaPairingDescOfEq (ModuleCat.{u} R) (MonObj.mul (X := A))
          0 q q (Nat.zero_add q)
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ =
        (ComonObj.counit (X := K) ▷ K).f q ≫ (λ_ K).hom.f q ≫ φ := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ιTensorObj_comp_linearYonedaPairingDescOfEq, hwhisk,
      ι_mapBifunctorMap_assoc]
    by_cases hi : i = 0
    · subst i
      have hs : 0 + j = q := h
      have hj : j = q := (Nat.zero_add j).symm.trans hs
      subst j
      simp only [dite_eq_left, curriedTensor_obj_obj, curriedTensor_map_app,
        HomologicalComplex.id_f, curriedTensor_obj_map, whiskerLeft_id,
        Category.id_comp]
      rw [hunitorPost]
      calc
        _ = ((ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom) ⊗ₘ φ) ≫
            (MonObj.one (X := A) ▷ A) ≫ MonObj.mul (X := A) := by
          rw [MonoidalCategory.tensorHom_comp_whiskerRight_assoc, Category.assoc]
        _ = ((ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom) ⊗ₘ φ) ≫ (λ_ A).hom := by
          rw [MonObj.one_mul]
        _ = _ := by
          rw [MonoidalCategory.tensorHom_def_assoc,
            MonoidalCategory.comp_whiskerRight_assoc,
            MonoidalCategory.leftUnitor_naturality]
    · simp only [dite_eq_right hi]
      have hcounit : ComonObj.counit (X := K).f i = 0 :=
        (isZero_single_obj_X (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R)) i hi).eq_of_tgt _ _
      rw [hcounit, Functor.map_zero]
      simp
  have htriangle : ComonObj.comul (X := K) ≫
      (ComonObj.counit (X := K) ▷ K) ≫ (λ_ K).hom = 𝟙 K := by
    rw [← Category.assoc, ComonObj.counit_comul, Iso.inv_hom_id]
  have hdegree := congrArg (fun f : K ⟶ K => f.f q) htriangle
  have hcore :
      (K.XIsoOfEq (Nat.zero_add q).symm).hom ≫ ComonObj.comul (X := K).f (0 + q) ≫
          linearYonedaPairingDesc (ModuleCat.{u} R) (MonObj.mul (X := A)) 0 q
            (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ = φ := by
    calc
      _ = ComonObj.comul (X := K).f q ≫
          linearYonedaPairingDescOfEq (ModuleCat.{u} R) (MonObj.mul (X := A))
            0 q q (Nat.zero_add q)
            (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ :=
        XIsoOfEq_comp_linearYonedaPairingDesc (ModuleCat.{u} R)
          (ComonObj.comul (X := K)) (MonObj.mul (X := A)) 0 q q
          (Nat.zero_add q).symm
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) φ
      _ = φ := by
        rw [hdesc]
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          Category.assoc, Category.id_comp] using
          congrArg (fun f : K.X q ⟶ K.X q => f ≫ φ) hdegree
  rw [linearHomCochainGradedPairing_pair]
  erw [linearHomCochainPair_tmul]
  erw [linearHomCochainComplex_XIsoOfEq_hom_apply]
  simpa only [linearHomCochainOne, linearHomPairingDesc, Category.assoc] using hcore

public theorem linearHomCochainPair_one_left (q : ℕ) :
    (linearHomCochainOneHom R K A ⊗ₘ
        𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair 0 q ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.zero_add q)).hom =
    (λ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)).hom := by
  apply (cancel_epi
    (λ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X q)).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have hunit : (linearHomCochainOneHom R K A).hom 1 =
      linearHomCochainOne R K A := by
    simpa only [linearHomCochainOne] using linearHomCochainOneHom_apply_one R K A
  simpa only [moduleHom_comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, moduleTensorHom_tmul,
    ModuleCat.hom_id, LinearMap.id_apply, hunit,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul] using
    linearHomCochainPair_one_left_apply R K A q φ

private lemma linearHomCochainPair_one_right_apply
    (p : ℕ)
    (φ : ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).X p) :
    ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
      (op K)).XIsoOfEq (Nat.add_zero p)).hom).hom
        (((linearHomCochainGradedPairing R (ComonObj.comul (X := K))
          (MonObj.mul (X := A))).pair p 0).hom
          (φ ⊗ₜ[R] linearHomCochainOne R K A)) = φ := by
  dsimp only [linearHomCochainComplexFunctor_obj_X] at φ ⊢
  have hcoord : (ρ_ K).inv.f p = (rightUnitor' K).inv p := rfl
  have hinv : (ρ_ K).inv.f p =
      (ρ_ (K.X p)).inv ≫
        (K.X p ◁ (singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).inv) ≫
            ιTensorObj K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
              p 0 p (Nat.add_zero p) := by
    rw [hcoord, rightUnitor'_inv]
    rfl
  have hcancel : (ρ_ K).hom.f p ≫ (ρ_ K).inv.f p =
      𝟙 ((K ⊗ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))).X p) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg
        (fun f : K ⊗ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) ⟶
            K ⊗ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)) => f.f p)
        (ρ_ K).hom_inv_id
  have hunitor :
      ιTensorObj K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
          p 0 p (Nat.add_zero p) ≫ (ρ_ K).hom.f p =
        (K.X p ◁ (singleObjXSelf (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R))).hom) ≫ (ρ_ (K.X p)).hom := by
    apply (cancel_mono ((ρ_ K).inv.f p)).mp
    calc
      _ = ιTensorObj K (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
          p 0 p (Nat.add_zero p) := by
        rw [Category.assoc, hcancel]
        exact Category.comp_id _
      _ = _ := by
        rw [hinv]
        simp only [Category.assoc, Iso.hom_inv_id_assoc,
          MonoidalCategory.whiskerLeft_hom_inv_assoc]
  have hunitorPost := congrArg
    (fun f : K.X p ⊗ (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).X 0 ⟶ K.X p =>
      f ≫ φ) hunitor
  simp only [Category.assoc] at hunitorPost
  have hwhisk : (K ◁ ComonObj.counit (X := K)).f p =
      (tensorHom (𝟙 K) (ComonObj.counit (X := K))).f p := rfl
  have hdesc :
      linearYonedaPairingDescOfEq (ModuleCat.{u} R) (MonObj.mul (X := A))
          p 0 p (Nat.add_zero p) φ
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) =
        (K ◁ ComonObj.counit (X := K)).f p ≫ (ρ_ K).hom.f p ≫ φ := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [ιTensorObj_comp_linearYonedaPairingDescOfEq, hwhisk,
      ι_mapBifunctorMap_assoc]
    by_cases hi : i = p
    · subst i
      have hs : p + j = p := h
      have hj : j = 0 := by omega
      subst j
      simp only [dite_eq_left, curriedTensor_obj_obj, curriedTensor_map_app,
        HomologicalComplex.id_f, curriedTensor_obj_map, id_whiskerRight,
        Category.id_comp]
      rw [hunitorPost]
      calc
        _ = (φ ⊗ₘ (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom)) ≫
            (A ◁ MonObj.one (X := A)) ≫ MonObj.mul (X := A) := by
          rw [MonoidalCategory.tensorHom_comp_whiskerLeft_assoc, Category.assoc]
        _ = (φ ⊗ₘ (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom)) ≫ (ρ_ A).hom := by
          rw [MonObj.mul_one]
        _ = _ := by
          rw [MonoidalCategory.tensorHom_def'_assoc,
            MonoidalCategory.whiskerLeft_comp_assoc,
            MonoidalCategory.rightUnitor_naturality]
    · have hj : j ≠ 0 := by
        intro hj
        subst j
        apply hi
        have hs : i + 0 = p := h
        exact (Nat.add_zero i).symm.trans hs
      simp only [dite_eq_right hi]
      have hcounit : ComonObj.counit (X := K).f j = 0 :=
        (isZero_single_obj_X (ComplexShape.down ℕ) 0
          (𝟙_ (ModuleCat.{u} R)) j hj).eq_of_tgt _ _
      rw [hcounit, Functor.map_zero]
      simp
  have htriangle : ComonObj.comul (X := K) ≫
      (K ◁ ComonObj.counit (X := K)) ≫ (ρ_ K).hom = 𝟙 K := by
    rw [← Category.assoc, ComonObj.comul_counit, Iso.inv_hom_id]
  have hdegree := congrArg (fun f : K ⟶ K => f.f p) htriangle
  have hcore :
      (K.XIsoOfEq (Nat.add_zero p).symm).hom ≫ ComonObj.comul (X := K).f (p + 0) ≫
          linearYonedaPairingDesc (ModuleCat.{u} R) (MonObj.mul (X := A)) p 0 φ
            (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) = φ := by
    calc
      _ = ComonObj.comul (X := K).f p ≫
          linearYonedaPairingDescOfEq (ModuleCat.{u} R) (MonObj.mul (X := A))
            p 0 p (Nat.add_zero p) φ
            (ComonObj.counit (X := K).f 0 ≫
              (singleObjXSelf (ComplexShape.down ℕ) 0
                (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A)) :=
        XIsoOfEq_comp_linearYonedaPairingDesc (ModuleCat.{u} R)
          (ComonObj.comul (X := K)) (MonObj.mul (X := A)) p 0 p
          (Nat.add_zero p).symm φ
          (ComonObj.counit (X := K).f 0 ≫
            (singleObjXSelf (ComplexShape.down ℕ) 0
              (𝟙_ (ModuleCat.{u} R))).hom ≫ MonObj.one (X := A))
      _ = φ := by
        rw [hdesc]
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          Category.assoc, Category.id_comp] using
          congrArg (fun f : K.X p ⟶ K.X p => f ≫ φ) hdegree
  rw [linearHomCochainGradedPairing_pair]
  erw [linearHomCochainPair_tmul]
  have hsum : (K.XIsoOfEq (Nat.add_zero p).symm).hom = 𝟙 (K.X p) := by
    rfl
  rw [hsum, Category.id_comp] at hcore
  simpa only [linearHomCochainOne, linearHomPairingDesc, Category.assoc] using hcore

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


public theorem linearHomCochainPair_one_right (p : ℕ) :
    (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p) ⊗ₘ
        linearHomCochainOneHom R K A) ≫
      (linearHomCochainGradedPairing R (ComonObj.comul (X := K))
        (MonObj.mul (X := A))).pair p 0 ≫
      (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
        (op K)).XIsoOfEq (Nat.add_zero p)).hom =
    (ρ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p)).hom := by
  apply (cancel_epi
    (ρ_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X p)).inv).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  have hunit : (linearHomCochainOneHom R K A).hom 1 =
      linearHomCochainOne R K A := by
    simpa only [linearHomCochainOne] using linearHomCochainOneHom_apply_one R K A
  simpa only [moduleHom_comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply, moduleTensorHom_tmul,
    ModuleCat.hom_id, LinearMap.id_apply, hunit,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, one_smul] using
    linearHomCochainPair_one_right_apply R K A p φ

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

/-- For nonnegative chain complexes K₁, K₂ of modules over a commutative
ring R with a total tensor product, let φ : K₁,p → M, ψ : K₂,q → N and
μ : M ⊗[R] N → P be R-linear maps. On a summand K₁,i ⊗[R] K₂,j with
i + j = p + q, the pairing descriptor is μ ∘ (φ ⊗ ψ) when i = p
(and hence j = q), using the degree identifications, and is zero otherwise. -/
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

/-- Let R be a commutative ring, K₁, K₂ nonnegative chain complexes with
a total tensor product, φ : K₁,p → R and f : K₂,q → N R-linear maps.
The descriptor formed from φ and the identity of K₂,q using the left
tensor unitor, followed by f, equals the descriptor formed from φ and f
using the left unitor of N. This equality expresses postcomposition
naturality of scalar multiplication on the selected (p, q) summand. -/
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
