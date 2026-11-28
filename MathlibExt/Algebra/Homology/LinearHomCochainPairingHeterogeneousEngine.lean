/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneousBasic

/-!
# Tensor descriptors and values of Hom cochain pairings

Let R be a commutative ring and work with nonnegative chain complexes and
coefficient modules of carrier universe u. For φ : K₁,p → M₁,
ψ : K₂,q → M₂, μ : M₁ ⊗[R] M₂ → M₃, and p + q = n, the tensor descriptor
from (K₁ ⊗ K₂)_n to M₃ is μ ∘ (φ ⊗ ψ) on the (p, q) summand and zero
elsewhere. It is natural under chain maps into K₁ and K₂ and under
identifications of the total degree.

A comparison from Hom_R(L; M) to Hom_R(K; N), determined by
f : K → L and a : M → N, sends φ to a ∘ φ ∘ f. Compatible coefficient
associativity diagrams identify the two ternary descriptors after the
tensor associator. A chain map ε : Kᵤ → R[0] and a coefficient map R → U
give a degree-zero cocycle; compatible counit and coefficient unit diagrams
make its left and right pairings equal to the input cochain after the
specified source and coefficient comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace HomologicalComplex.LinearHomCochainPairingHeterogeneous

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomHeterogeneousEngineChainComplexMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

noncomputable def heterogeneousLinearHomPairingDescOfEq
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (μ : M₁ ⊗ M₂ ⟶ M₃) (p q n : ℕ) (hpq : p + q = n)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    (tensorObj K₁ K₂).X n ⟶ M₃ :=
  linearYonedaPairingDescOfEq (ModuleCat.{u} R) μ p q n hpq φ ψ

@[reassoc]
lemma ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (μ : M₁ ⊗ M₂ ⟶ M₃) (p q n i j : ℕ)
    (hpq : p + q = n) (hij : i + j = n)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    ιTensorObj K₁ K₂ i j n hij ≫
        heterogeneousLinearHomPairingDescOfEq R μ p q n hpq φ ψ =
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
lemma ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_of_eq
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (μ : M₁ ⊗ M₂ ⟶ M₃) (p q n i j : ℕ)
    (hpq : p + q = n) (hij : i + j = n)
    (hi : i = p) (hj : j = q)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    ιTensorObj K₁ K₂ i j n hij ≫
        heterogeneousLinearHomPairingDescOfEq R μ p q n hpq φ ψ =
      ((K₁.XIsoOfEq hi).hom ⊗ₘ (K₂.XIsoOfEq hj).hom) ≫
        (φ ⊗ₘ ψ) ≫ μ := by
  subst i
  subst j
  rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
  simp

lemma linearHomPairingDesc_eq_heterogeneous
    {K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (μ : M₁ ⊗ M₂ ⟶ M₃) (p q : ℕ)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    linearHomPairingDesc R μ p q φ ψ =
      heterogeneousLinearHomPairingDescOfEq R μ p q (p + q) rfl φ ψ := by
  apply mapBifunctor.hom_ext
  intro i j hij
  rw [ιTensorObj_comp_linearHomPairingDesc,
    ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel hij
    subst j
    simp
  · simp [hi]

@[simp]
lemma linearHomCochainComplex_XIsoOfEq_hom_apply'
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R)
    {p q : ℕ} (h : p = q) (φ : K.X p ⟶ M) :
    (((linearHomCochainComplex R K M).XIsoOfEq h).hom).hom φ =
      (K.XIsoOfEq h.symm).hom ≫ φ := by
  subst q
  rfl

@[simp]
lemma linearHomCochainComparison_f_apply
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    {M N : ModuleCat.{u} R} (f : K ⟶ L) (a : M ⟶ N)
    (n : ℕ) (φ : L.X n ⟶ M) :
    ((linearHomCochainComparison R f a).f n).hom φ =
      f.f n ≫ φ ≫ a := by
  rfl

@[reassoc]
lemma XIsoOfEq_comp_heterogeneousLinearHomPairingDesc
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ} [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (Δ : K₃ ⟶ tensorObj K₁ K₂) (μ : M₁ ⊗ M₂ ⟶ M₃)
    (p q n : ℕ) (h : n = p + q)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    (K₃.XIsoOfEq h).hom ≫ Δ.f (p + q) ≫
        linearHomPairingDesc R μ p q φ ψ =
      Δ.f n ≫ heterogeneousLinearHomPairingDescOfEq R μ p q n h.symm φ ψ := by
  subst n
  simp only [XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  rw [linearHomPairingDesc_eq_heterogeneous]

lemma heterogeneousLinearHomPairingDescOfEq_naturality
    {L₁ L₂ K₁ K₂ : ChainComplex (ModuleCat.{u} R) ℕ}
    [HasTensor L₁ L₂] [HasTensor K₁ K₂]
    {M₁ M₂ M₃ : ModuleCat.{u} R}
    (f₁ : L₁ ⟶ K₁) (f₂ : L₂ ⟶ K₂)
    (μ : M₁ ⊗ M₂ ⟶ M₃) (p q n : ℕ) (hpq : p + q = n)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) :
    (tensorHom f₁ f₂).f n ≫
        heterogeneousLinearHomPairingDescOfEq R μ p q n hpq φ ψ =
      heterogeneousLinearHomPairingDescOfEq R μ p q n hpq
        (f₁.f p ≫ φ) (f₂.f q ≫ ψ) := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [← Category.assoc, ι_mapBifunctorMap]
  simp only [Category.assoc]
  rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq,
    ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
  change i + j = n at h
  by_cases hi : i = p
  · subst i
    have hj : j = q := by omega
    subst j
    simp only [dite_eq_left]
    change (f₁.f p ▷ L₂.X q) ≫ (K₁.X p ◁ f₂.f q) ≫
        (φ ⊗ₘ ψ) ≫ μ =
      ((f₁.f p ≫ φ) ⊗ₘ (f₂.f q ≫ ψ)) ≫ μ
    rw [← MonoidalCategory.tensorHom_def_assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  · simp [hi]

lemma heterogeneousLinearHomPairing_assoc
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : ModuleCat.{u} R}
    (μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (μₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (μᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hμ : (μ₁₂ ▷ M₃) ≫ μₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ μ₂₃) ≫ μᵣ)
    (p q r : ℕ)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) (χ : K₃.X r ⟶ M₃) :
    (α_ (K₁.X p) (K₂.X q) (K₃.X r)).hom ≫
        (φ ⊗ₘ ((ψ ⊗ₘ χ) ≫ μ₂₃)) ≫ μᵣ =
      (((φ ⊗ₘ ψ) ≫ μ₁₂) ⊗ₘ χ) ≫ μₗ ≫ a := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  have h := congrArg
    (fun f => f.hom ((φ.hom x ⊗ₜ[R] ψ.hom y) ⊗ₜ[R] χ.hom z)) hμ
  exact h.symm

lemma heterogeneousLinearHomPairingDesc_assoc
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : ModuleCat.{u} R}
    (μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (μₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (μᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hμ : (μ₁₂ ▷ M₃) ≫ μₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ μ₂₃) ≫ μᵣ)
    (p q r n : ℕ) (hleft : (p + q) + r = n)
    (hright : p + (q + r) = n)
    (φ : K₁.X p ⟶ M₁) (ψ : K₂.X q ⟶ M₂) (χ : K₃.X r ⟶ M₃) :
    (HomologicalComplex.associator K₁ K₂ K₃).hom.f n ≫
        heterogeneousLinearHomPairingDescOfEq R μᵣ p (q + r) n
          hright φ (linearHomPairingDesc R μ₂₃ q r ψ χ) =
      heterogeneousLinearHomPairingDescOfEq R μₗ (p + q) r n
        hleft (linearHomPairingDesc R μ₁₂ p q φ ψ) χ ≫ a := by
  subst n
  apply mapBifunctor₁₂.hom_ext
  intro i j k h
  have hassoc := ι_mapBifunctorAssociatorX_hom_assoc
    (curriedAssociatorNatIso (ModuleCat.{u} R)) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j k ((p + q) + r) h
    (heterogeneousLinearHomPairingDescOfEq R μᵣ p (q + r) ((p + q) + r)
      hright φ (linearHomPairingDesc R μ₂₃ q r ψ χ))
  change _ ≫ (HomologicalComplex.associator K₁ K₂ K₃).hom.f ((p + q) + r) ≫ _ =
    (α_ (K₁.X i) (K₂.X j) (K₃.X k)).hom ≫ _ ≫ _ at hassoc
  rw [hassoc]
  change i + j + k = (p + q) + r at h
  have h23 := mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{u} R))
    (curriedTensor (ModuleCat.{u} R)) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j k (j + k) ((p + q) + r) rfl
      (by change i + (j + k) = (p + q) + r; omega)
  have h12 := mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{u} R))
    (curriedTensor (ModuleCat.{u} R)) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j k (i + j) ((p + q) + r) rfl h
  rw [h23, h12]
  simp only [Category.assoc]
  by_cases hi : i = p
  · subst i
    by_cases hj : j = q
    · subst j
      have hk : k = r := by omega
      subst k
      slice_lhs 3 4 =>
        rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_of_eq
          R μᵣ p (q + r) ((p + q) + r) p (q + r) hright
            (by omega) rfl rfl φ
            (linearHomPairingDesc R μ₂₃ q r ψ χ)]
      slice_rhs 2 3 =>
        rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_of_eq
          R μₗ (p + q) r ((p + q) + r) (p + q) r rfl h rfl rfl
            (linearHomPairingDesc R μ₁₂ p q φ ψ) χ]
      simp only [curriedTensor_obj_obj, curriedTensor_obj_map, XIsoOfEq_rfl,
        Iso.refl_hom, tensorHom_id, id_whiskerRight, Category.id_comp,
        curriedTensor_map_app, Category.assoc]
      change (α_ (K₁.X p) (K₂.X q) (K₃.X r)).hom ≫
          (K₁.X p ◁ ιTensorObj K₂ K₃ q r (q + r) rfl) ≫
            (φ ⊗ₘ linearHomPairingDesc R μ₂₃ q r ψ χ) ≫ μᵣ =
        (ιTensorObj K₁ K₂ p q (p + q) rfl ▷ K₃.X r) ≫
          (linearHomPairingDesc R μ₁₂ p q φ ψ ⊗ₘ χ) ≫ μₗ ≫ a
      erw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]
      rw [linearHomPairingDesc_eq_heterogeneous]
      rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
      simp only [dite_eq_left]
      rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
      rw [linearHomPairingDesc_eq_heterogeneous]
      rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
      simp only [dite_eq_left]
      exact heterogeneousLinearHomPairing_assoc R μ₁₂ μₗ μ₂₃ μᵣ a hμ
        p q r φ ψ χ
    · have hpj : ¬p + j = p + q := by
        intro hpj
        exact hj (Nat.add_left_cancel hpj)
      have hjk : j + k = q + r := by omega
      slice_lhs 3 4 =>
        rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_of_eq
          R μᵣ p (q + r) ((p + q) + r) p (j + k) hright
            (by omega) rfl hjk φ
            (linearHomPairingDesc R μ₂₃ q r ψ χ)]
      rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_assoc]
      simp only [dite_eq_right hpj]
      simp only [XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_obj_map]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp]
      have htransport :
          ((tensorObj K₂ K₃).XIsoOfEq hjk).hom ≫
              linearHomPairingDesc R μ₂₃ q r ψ χ =
            heterogeneousLinearHomPairingDescOfEq R μ₂₃
              q r (j + k) hjk.symm ψ χ := by
        simpa [linearHomPairingDesc_eq_heterogeneous] using
          XIsoOfEq_comp_heterogeneousLinearHomPairingDesc R
            (𝟙 (tensorObj K₂ K₃)) μ₂₃ q r (j + k) hjk ψ χ
      rw [htransport]
      rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]
      rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
      simp [hj]
  · by_cases hij : i + j = p + q
    · slice_lhs 3 4 =>
        rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
      simp only [dite_eq_right hi, CategoryTheory.Limits.comp_zero]
      have hk : k = r := by omega
      subst k
      slice_rhs 2 3 =>
        rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_of_eq
          R μₗ (p + q) r ((p + q) + r) (i + j) r rfl
            (by omega) hij rfl
            (linearHomPairingDesc R μ₁₂ p q φ ψ) χ]
      simp only [XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_map_app]
      simp only [Category.assoc]
      rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp, Category.assoc]
      have htransport :
          ((tensorObj K₁ K₂).XIsoOfEq hij).hom ≫
              linearHomPairingDesc R μ₁₂ p q φ ψ =
            heterogeneousLinearHomPairingDescOfEq R μ₁₂
              p q (i + j) hij.symm φ ψ := by
        simpa [linearHomPairingDesc_eq_heterogeneous] using
          XIsoOfEq_comp_heterogeneousLinearHomPairingDesc R
            (𝟙 (tensorObj K₁ K₂)) μ₁₂ p q (i + j) hij φ ψ
      rw [htransport, ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq]
      simp [hi]
    · rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq,
        ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_assoc]
      simp [hi, hij]

lemma heterogeneousLinearHomPairingDesc_left_unit
    {Kᵤ K : ChainComplex (ModuleCat.{u} R) ℕ}
    {U M L : ModuleCat.{u} R}
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : U ⊗ M ⟶ L) (a : L ⟶ M)
    (hμ : (e ▷ M) ≫ μ ≫ a = (λ_ M).hom)
    (q : ℕ) (φ : K.X q ⟶ M) :
    heterogeneousLinearHomPairingDescOfEq R μ 0 q q (Nat.zero_add q)
        (linearHomCochainUnitOfCounit R Kᵤ ε U e) φ ≫ a =
      (ε ▷ K).f q ≫ (λ_ K).hom.f q ≫ φ := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_assoc]
  change _ = ιTensorObj Kᵤ K i j q h ≫
    (tensorHom ε (𝟙 K)).f q ≫ (λ_ K).hom.f q ≫ φ
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
    rw [linearHomCochainUnitOfCounit]
    rw [MonoidalCategory.tensorHom_def_assoc]
    rw [MonoidalCategory.comp_whiskerRight_assoc,
      MonoidalCategory.comp_whiskerRight_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc]
    simp only [Category.assoc]
    rw [hμ]
    slice_lhs 3 4 => rw [MonoidalCategory.leftUnitor_naturality]
  · simp only [dite_eq_right hi]
    have hε : ε.f i = 0 := by
      apply (isZero_single_obj_X (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R)) i hi).eq_of_tgt
    rw [hε, Functor.map_zero]
    simp

lemma linearHomCochainPair_left_unit_apply
    {Kᵤ K Kₗ : ChainComplex (ModuleCat.{u} R) ℕ}
    {U M L : ModuleCat.{u} R}
    (Δ : Kₗ ⟶ Kᵤ ⊗ K)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (c : K ⟶ Kₗ)
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : U ⊗ M ⟶ L) (a : L ⟶ M)
    (hΔ : c ≫ Δ ≫ (ε ▷ K) ≫ (λ_ K).hom = 𝟙 K)
    (hμ : (e ▷ M) ≫ μ ≫ a = (λ_ M).hom)
    (q : ℕ) (φ : K.X q ⟶ M) :
    (((linearHomCochainComplex R K M).XIsoOfEq (Nat.zero_add q)).hom).hom
        (((linearHomCochainComparison R c a).f (0 + q)).hom
          (((linearHomCochainGradedPairing R Δ μ).pair 0 q).hom
            (linearHomCochainUnitOfCounit R Kᵤ ε U e ⊗ₜ[R] φ))) = φ := by
  erw [linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainComparison_f_apply,
    linearHomCochainComplex_XIsoOfEq_hom_apply']
  change (K.XIsoOfEq (Nat.zero_add q).symm).hom ≫
      (c ≫ Δ).f (0 + q) ≫
        linearHomPairingDesc R μ 0 q
          (linearHomCochainUnitOfCounit R Kᵤ ε U e) φ ≫ a = φ
  rw [XIsoOfEq_comp_heterogeneousLinearHomPairingDesc_assoc R
    (c ≫ Δ) μ 0 q q (Nat.zero_add q).symm
    (linearHomCochainUnitOfCounit R Kᵤ ε U e) φ]
  rw [heterogeneousLinearHomPairingDesc_left_unit R ε e μ a hμ q φ]
  change c.f q ≫ Δ.f q ≫ (ε ▷ K).f q ≫ (λ_ K).hom.f q ≫ φ = φ
  have hΔq := congrArg (fun f => f.f q) hΔ
  dsimp only [HomologicalComplex.comp_f] at hΔq
  simpa only [Category.assoc, id_f, Category.id_comp] using
    congrArg (fun f => f ≫ φ) hΔq

lemma heterogeneousLinearHomPairingDesc_right_unit
    {K Kᵤ : ChainComplex (ModuleCat.{u} R) ℕ}
    {M U L : ModuleCat.{u} R}
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : M ⊗ U ⟶ L) (a : L ⟶ M)
    (hμ : (M ◁ e) ≫ μ ≫ a = (ρ_ M).hom)
    (p : ℕ) (φ : K.X p ⟶ M) :
    heterogeneousLinearHomPairingDescOfEq R μ p 0 p (Nat.add_zero p) φ
        (linearHomCochainUnitOfCounit R Kᵤ ε U e) ≫ a =
      (K ◁ ε).f p ≫ (ρ_ K).hom.f p ≫ φ := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [ιTensorObj_comp_heterogeneousLinearHomPairingDescOfEq_assoc]
  change _ = ιTensorObj K Kᵤ i j p h ≫
    (tensorHom (𝟙 K) ε).f p ≫ (ρ_ K).hom.f p ≫ φ
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
    rw [linearHomCochainUnitOfCounit]
    rw [MonoidalCategory.tensorHom_def_assoc]
    rw [MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← MonoidalCategory.whisker_exchange_assoc,
      ← MonoidalCategory.whisker_exchange_assoc]
    simp only [Category.assoc]
    rw [hμ]
    slice_lhs 3 4 => rw [MonoidalCategory.rightUnitor_naturality]
  · have hj : j ≠ 0 := by
      intro hj
      subst j
      apply hi
      simpa using h
    simp only [dite_eq_right hi]
    have hε : ε.f j = 0 := by
      apply (isZero_single_obj_X (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R)) j hj).eq_of_tgt
    rw [hε, Functor.map_zero]
    simp

lemma linearHomCochainPair_right_unit_apply
    {K Kᵤ Kₗ : ChainComplex (ModuleCat.{u} R) ℕ}
    {M U L : ModuleCat.{u} R}
    (Δ : Kₗ ⟶ K ⊗ Kᵤ)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (c : K ⟶ Kₗ)
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U) (μ : M ⊗ U ⟶ L) (a : L ⟶ M)
    (hΔ : c ≫ Δ ≫ (K ◁ ε) ≫ (ρ_ K).hom = 𝟙 K)
    (hμ : (M ◁ e) ≫ μ ≫ a = (ρ_ M).hom)
    (p : ℕ) (φ : K.X p ⟶ M) :
    (((linearHomCochainComplex R K M).XIsoOfEq (Nat.add_zero p)).hom).hom
        (((linearHomCochainComparison R c a).f (p + 0)).hom
          (((linearHomCochainGradedPairing R Δ μ).pair p 0).hom
            (φ ⊗ₜ[R] linearHomCochainUnitOfCounit R Kᵤ ε U e))) = φ := by
  erw [linearHomCochainGradedPairing_pair, linearHomCochainPair_tmul,
    linearHomCochainComparison_f_apply]
  change c.f p ≫ Δ.f p ≫ linearHomPairingDesc R μ p 0 φ
      (linearHomCochainUnitOfCounit R Kᵤ ε U e) ≫ a = φ
  rw [linearHomPairingDesc_eq_heterogeneous]
  simp only [Nat.add_zero]
  rw [heterogeneousLinearHomPairingDesc_right_unit R ε e μ a hμ p φ]
  have hΔp := congrArg (fun f => f.f p) hΔ
  dsimp only [HomologicalComplex.comp_f] at hΔp
  simpa only [Category.assoc, id_f, Category.id_comp] using
    congrArg (fun f => f ≫ φ) hΔp

end HomologicalComplex.LinearHomCochainPairingHeterogeneous
