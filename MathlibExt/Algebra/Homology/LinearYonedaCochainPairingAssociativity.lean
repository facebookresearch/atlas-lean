/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.BifunctorAssociator
public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairing

/-!
# Associativity of linear Yoneda cochain pairings

Let R be a commutative ring in universe v and C a preadditive R-linear
monoidal category, with objects in universe u and morphisms in universe v.
Tensoring is additive and R-linear in each variable. Nonnegative chain
complexes in C give Hom cochain complexes of R-modules. All tensor products
of chain complexes appearing in the associativity diagrams are assumed to exist.

Four chain diagonals and four coefficient pairings can have distinct
intermediate and output objects. The comparisons c : Kᵣ → Kₗ and
a : Mₗ → Mᵣ act on Hom cochains by φ ↦ a ∘ φ ∘ c.
If α ∘ (Δ₁₂ ⊗ id) ∘ Δₗ ∘ c = (id ⊗ Δ₂₃) ∘ Δᵣ and
a ∘ μₗ ∘ (μ₁₂ ⊗ id) = μᵣ ∘ (id ⊗ μ₂₃) ∘ α, the two ternary
Hom pairings agree after this comparison and the degree identification
(p + q) + r = p + (q + r).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe v u

namespace HomologicalComplex

variable (R : Type v) [CommRing R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]

omit [MonoidalPreadditive C] in
private lemma linearYonedaCoefficientPairing_assoc
    {K₁ K₂ K₃ : ChainComplex C ℕ}
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : C}
    (mu₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (muₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (mu₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (muᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hmu : (mu₁₂ ▷ M₃) ≫ muₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ mu₂₃) ≫ muᵣ)
    (p q r : ℕ)
    (phi : K₁.X p ⟶ M₁) (psi : K₂.X q ⟶ M₂) (chi : K₃.X r ⟶ M₃) :
    (α_ (K₁.X p) (K₂.X q) (K₃.X r)).hom ≫
        (phi ⊗ₘ ((psi ⊗ₘ chi) ≫ mu₂₃)) ≫ muᵣ =
      (((phi ⊗ₘ psi) ≫ mu₁₂) ⊗ₘ chi) ≫ muₗ ≫ a := by
  rw [← MonoidalCategory.tensorHom_comp_whiskerLeft_assoc]
  rw [← Category.assoc, ← MonoidalCategory.associator_naturality]
  simp only [Category.assoc]
  rw [← hmu]
  rw [MonoidalCategory.tensorHom_comp_whiskerRight_assoc]

/-- In a preadditive R-linear monoidal category C over a commutative ring
R, with tensor product additive and R-linear in each variable, let
K₁, K₂, K₃ be nonnegative chain complexes for which both binary and both
parenthesized ternary tensor products exist. Suppose
μ₁₂ : M₁ ⊗ M₂ → M₁₂, μₗ : M₁₂ ⊗ M₃ → Mₗ,
μ₂₃ : M₂ ⊗ M₃ → M₂₃, μᵣ : M₁ ⊗ M₂₃ → Mᵣ and a : Mₗ → Mᵣ satisfy
a ∘ μₗ ∘ (μ₁₂ ⊗ id) = μᵣ ∘ (id ⊗ μ₂₃) ∘ α.
For cochains of degrees p, q, r and a common n = (p + q) + r = p + (q + r),
the left-associated tensor descriptor followed by a equals the right-associated
descriptor precomposed with the chain tensor associator in degree n. -/
theorem linearYonedaPairingDesc_assoc
    {K₁ K₂ K₃ : ChainComplex C ℕ}
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃]
    [HasTensor K₁ (tensorObj K₂ K₃)]
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : C}
    (mu₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (muₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (mu₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (muᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hmu : (mu₁₂ ▷ M₃) ≫ muₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ mu₂₃) ≫ muᵣ)
    (p q r n : ℕ) (hleft : (p + q) + r = n)
    (hright : p + (q + r) = n)
    (phi : K₁.X p ⟶ M₁) (psi : K₂.X q ⟶ M₂) (chi : K₃.X r ⟶ M₃) :
    (HomologicalComplex.associator K₁ K₂ K₃).hom.f n ≫
        linearYonedaPairingDescOfEq C muᵣ p (q + r) n
          hright phi (linearYonedaPairingDesc C mu₂₃ q r psi chi) =
      linearYonedaPairingDescOfEq C muₗ (p + q) r n
        hleft (linearYonedaPairingDesc C mu₁₂ p q phi psi) chi ≫ a := by
  subst n
  apply mapBifunctor₁₂.hom_ext
  intro i j l h
  have hassoc := ι_mapBifunctorAssociatorX_hom_assoc
    (curriedAssociatorNatIso C) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j l ((p + q) + r) h
    (linearYonedaPairingDescOfEq C muᵣ p (q + r) ((p + q) + r)
      hright phi (linearYonedaPairingDesc C mu₂₃ q r psi chi))
  change _ ≫ (HomologicalComplex.associator K₁ K₂ K₃).hom.f ((p + q) + r) ≫ _ =
    (α_ (K₁.X i) (K₂.X j) (K₃.X l)).hom ≫ _ ≫ _ at hassoc
  rw [hassoc]
  change i + j + l = (p + q) + r at h
  have h23 := mapBifunctor₂₃.ι_eq (curriedTensor C)
    (curriedTensor C) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j l (j + l) ((p + q) + r) rfl
      (by change i + (j + l) = (p + q) + r; omega)
  have h12 := mapBifunctor₁₂.ι_eq (curriedTensor C)
    (curriedTensor C) K₁ K₂ K₃
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    i j l (i + j) ((p + q) + r) rfl h
  rw [h23, h12]
  simp only [Category.assoc]
  by_cases hi : i = p
  · subst i
    by_cases hj : j = q
    · subst j
      have hl : l = r := by omega
      subst l
      slice_lhs 3 4 =>
        rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
          (C := C) muᵣ p (q + r) ((p + q) + r) p (q + r) hright
            (by omega) rfl rfl phi
            (linearYonedaPairingDesc C mu₂₃ q r psi chi)]
      slice_rhs 2 3 =>
        rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
          (C := C) muₗ (p + q) r ((p + q) + r) (p + q) r rfl h rfl rfl
            (linearYonedaPairingDesc C mu₁₂ p q phi psi) chi]
      simp only [curriedTensor_obj_obj, curriedTensor_obj_map, XIsoOfEq_rfl,
        Iso.refl_hom, tensorHom_id, id_whiskerRight, Category.id_comp,
        curriedTensor_map_app, Category.assoc]
      change (α_ (K₁.X p) (K₂.X q) (K₃.X r)).hom ≫
          (K₁.X p ◁ ιTensorObj K₂ K₃ q r (q + r) rfl) ≫
            (phi ⊗ₘ linearYonedaPairingDesc C mu₂₃ q r psi chi) ≫ muᵣ =
        (ιTensorObj K₁ K₂ p q (p + q) rfl ▷ K₃.X r) ≫
          (linearYonedaPairingDesc C mu₁₂ p q phi psi ⊗ₘ chi) ≫ muₗ ≫ a
      erw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]
      unfold linearYonedaPairingDesc
      rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
      simp only [dite_eq_left]
      rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc,
        ιTensorObj_comp_linearYonedaPairingDescOfEq]
      simp only [dite_eq_left]
      exact linearYonedaCoefficientPairing_assoc C mu₁₂ muₗ mu₂₃ muᵣ a hmu
        p q r phi psi chi
    · have hpj : ¬p + j = p + q := by
        intro hpj
        exact hj (Nat.add_left_cancel hpj)
      have hjl : j + l = q + r := by omega
      slice_lhs 3 4 =>
        rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
          (C := C) muᵣ p (q + r) ((p + q) + r) p (j + l) hright
            (by omega) rfl hjl phi
            (linearYonedaPairingDesc C mu₂₃ q r psi chi)]
      rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_assoc]
      simp only [dite_eq_right hpj]
      simp only [XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_obj_map]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp]
      have htransport :
          ((tensorObj K₂ K₃).XIsoOfEq hjl).hom ≫
              linearYonedaPairingDesc C mu₂₃ q r psi chi =
            linearYonedaPairingDescOfEq C mu₂₃
              q r (j + l) hjl.symm psi chi := by
        simpa [linearYonedaPairingDesc] using
          XIsoOfEq_comp_linearYonedaPairingDesc C (K₃ := tensorObj K₂ K₃)
            (𝟙 (tensorObj K₂ K₃)) mu₂₃ q r (j + l) hjl psi chi
      rw [htransport]
      rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]
      rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
      simp [hj]
  · by_cases hij : i + j = p + q
    · slice_lhs 3 4 =>
        rw [ιTensorObj_comp_linearYonedaPairingDescOfEq]
      simp only [dite_eq_right hi, CategoryTheory.Limits.comp_zero]
      have hl : l = r := by omega
      subst l
      slice_rhs 2 3 =>
        rw [ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
          (C := C) muₗ (p + q) r ((p + q) + r) (i + j) r rfl
            (by omega) hij rfl
            (linearYonedaPairingDesc C mu₁₂ p q phi psi) chi]
      simp only [XIsoOfEq_rfl, Iso.refl_hom, curriedTensor_map_app]
      simp only [Category.assoc]
      rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      simp only [Category.id_comp, Category.assoc]
      have htransport :
          ((tensorObj K₁ K₂).XIsoOfEq hij).hom ≫
              linearYonedaPairingDesc C mu₁₂ p q phi psi =
            linearYonedaPairingDescOfEq C mu₁₂
              p q (i + j) hij.symm phi psi := by
        simpa [linearYonedaPairingDesc] using
          XIsoOfEq_comp_linearYonedaPairingDesc C (K₃ := tensorObj K₁ K₂)
            (𝟙 (tensorObj K₁ K₂)) mu₁₂ p q (i + j) hij phi psi
      rw [htransport, ιTensorObj_comp_linearYonedaPairingDescOfEq]
      simp [hi]
    · rw [ιTensorObj_comp_linearYonedaPairingDescOfEq,
        ιTensorObj_comp_linearYonedaPairingDescOfEq_assoc]
      simp [hi, hij]

/-- In a preadditive R-linear monoidal category C over a commutative ring
R, with tensor product additive and R-linear in each variable, a chain map
f : K → L between nonnegative complexes and a coefficient map a : M → N
induce Hom_C(L; M) → Hom_C(K; N). In degree n, this cochain map sends
φ : L_n → M to a ∘ φ ∘ f_n. -/
noncomputable def linearYonedaCochainComparison
    {K L : ChainComplex C ℕ} {M N : C}
    (f : K ⟶ L) (a : M ⟶ N) :
    (linearHomCochainComplexFunctor R C M).obj (op L) ⟶
      (linearHomCochainComplexFunctor R C N).obj (op K) :=
  (linearHomCochainComplexFunctor R C M).map f.op ≫
    ((linearHomCochainComplexBifunctor R C).map a).app (op K)

omit [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] in
@[simp]
theorem linearYonedaCochainComparison_f_apply
    {K L : ChainComplex C ℕ} {M N : C}
    (f : K ⟶ L) (a : M ⟶ N) (n : ℕ) (phi : L.X n ⟶ M) :
    ((linearYonedaCochainComparison R C f a).f n).hom phi =
      f.f n ≫ phi ≫ a := by
  simp only [linearHomCochainComplexFunctor_obj_X,
    linearYonedaCochainComparison, NatTrans.naturality, comp_f,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  change f.f n ≫ (phi ≫ a) = f.f n ≫ phi ≫ a
  rfl


/-- In a preadditive R-linear monoidal category C over a commutative ring
R, with tensor product additive and R-linear in each variable, let the
nonnegative complexes Kᵢ carry diagonals
Δ₁₂ : K₁₂ → K₁ ⊗ K₂, Δₗ : Kₗ → K₁₂ ⊗ K₃,
Δ₂₃ : K₂₃ → K₂ ⊗ K₃, and Δᵣ : Kᵣ → K₁ ⊗ K₂₃.
Assume that these tensor products and both parenthesized tensors of K₁, K₂, K₃
exist. Let c : Kᵣ → Kₗ and coefficient maps μ₁₂, μₗ, μ₂₃, μᵣ, a : Mₗ → Mᵣ
satisfy α ∘ (Δ₁₂ ⊗ id) ∘ Δₗ ∘ c = (id ⊗ Δ₂₃) ∘ Δᵣ and
a ∘ μₗ ∘ (μ₁₂ ⊗ id) = μᵣ ∘ (id ⊗ μ₂₃) ∘ α.
Then the left-associated degree (p + q) + r Hom pairing followed by
φ ↦ a ∘ φ ∘ c and the degree identification equals the right-associated
degree p + (q + r) pairing, with the associator on its three input Hom modules. -/
theorem linearYonedaCochainPair_associativity_of_diagrams
    {K₁ K₂ K₃ K₁₂ K₂₃ Kₗ Kᵣ : ChainComplex C ℕ}
    [HasTensor K₁ K₂] [HasTensor K₁₂ K₃]
    [HasTensor K₂ K₃] [HasTensor K₁ K₂₃]
    [HasTensor (tensorObj K₁ K₂) K₃]
    [HasTensor K₁ (tensorObj K₂ K₃)]
    {M₁ M₂ M₃ M₁₂ M₂₃ Mₗ Mᵣ : C}
    (Delta₁₂ : K₁₂ ⟶ tensorObj K₁ K₂)
    (Deltaₗ : Kₗ ⟶ tensorObj K₁₂ K₃)
    (Delta₂₃ : K₂₃ ⟶ tensorObj K₂ K₃)
    (Deltaᵣ : Kᵣ ⟶ tensorObj K₁ K₂₃)
    (c : Kᵣ ⟶ Kₗ)
    (mu₁₂ : M₁ ⊗ M₂ ⟶ M₁₂) (muₗ : M₁₂ ⊗ M₃ ⟶ Mₗ)
    (mu₂₃ : M₂ ⊗ M₃ ⟶ M₂₃) (muᵣ : M₁ ⊗ M₂₃ ⟶ Mᵣ)
    (a : Mₗ ⟶ Mᵣ)
    (hDelta : c ≫ Deltaₗ ≫ tensorHom Delta₁₂ (𝟙 K₃) ≫
        (HomologicalComplex.associator K₁ K₂ K₃).hom =
      Deltaᵣ ≫ tensorHom (𝟙 K₁) Delta₂₃)
    (hmu : (mu₁₂ ▷ M₃) ≫ muₗ ≫ a =
      (α_ M₁ M₂ M₃).hom ≫ (M₁ ◁ mu₂₃) ≫ muᵣ)
    (p q r : ℕ) :
    ((linearYonedaCochainGradedPairing R C Delta₁₂ mu₁₂).pair p q ⊗ₘ
        𝟙 (((linearHomCochainComplexFunctor R C M₃).obj (op K₃)).X r)) ≫
      (linearYonedaCochainGradedPairing R C Deltaₗ muₗ).pair (p + q) r ≫
      (linearYonedaCochainComparison R C c a).f ((p + q) + r) ≫
      (((linearHomCochainComplexFunctor R C Mᵣ).obj (op Kᵣ)).XIsoOfEq
        (Nat.add_assoc p q r)).hom =
    (α_ (((linearHomCochainComplexFunctor R C M₁).obj (op K₁)).X p)
      (((linearHomCochainComplexFunctor R C M₂).obj (op K₂)).X q)
      (((linearHomCochainComplexFunctor R C M₃).obj (op K₃)).X r)).hom ≫
      (𝟙 (((linearHomCochainComplexFunctor R C M₁).obj (op K₁)).X p) ⊗ₘ
        (linearYonedaCochainGradedPairing R C Delta₂₃ mu₂₃).pair q r) ≫
      (linearYonedaCochainGradedPairing R C Deltaᵣ muᵣ).pair p (q + r) := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro phi psi chi
  dsimp only [linearHomCochainComplexFunctor_obj_X] at phi psi chi
  have hDeltaN := congrArg
    (fun F : Kᵣ ⟶ tensorObj K₁ (tensorObj K₂ K₃) => F.f (p + (q + r))) hDelta
  simp only [HomologicalComplex.comp_f] at hDeltaN
  have hpair :
      (Kᵣ.XIsoOfEq (Nat.add_assoc p q r).symm).hom ≫
          c.f ((p + q) + r) ≫ Deltaₗ.f ((p + q) + r) ≫
            linearYonedaPairingDesc C muₗ (p + q) r
              (Delta₁₂.f (p + q) ≫ linearYonedaPairingDesc C mu₁₂ p q phi psi)
              chi ≫ a =
        Deltaᵣ.f (p + (q + r)) ≫ linearYonedaPairingDesc C muᵣ p (q + r) phi
          (Delta₂₃.f (q + r) ≫ linearYonedaPairingDesc C mu₂₃ q r psi chi) := by
    calc
      _ = (Kᵣ.XIsoOfEq (Nat.add_assoc p q r).symm).hom ≫
          (c ≫ Deltaₗ).f ((p + q) + r) ≫
            linearYonedaPairingDesc C muₗ (p + q) r
              (Delta₁₂.f (p + q) ≫ linearYonedaPairingDesc C mu₁₂ p q phi psi)
              chi ≫ a := by simp only [HomologicalComplex.comp_f, Category.assoc]
      _ = (c ≫ Deltaₗ).f (p + (q + r)) ≫
          linearYonedaPairingDescOfEq C muₗ (p + q) r (p + (q + r))
            (Nat.add_assoc p q r)
            (Delta₁₂.f (p + q) ≫ linearYonedaPairingDesc C mu₁₂ p q phi psi)
            chi ≫ a := by
        rw [XIsoOfEq_comp_linearYonedaPairingDesc_assoc C
          (c ≫ Deltaₗ) muₗ (p + q) r (p + (q + r)) (Nat.add_assoc p q r).symm
          (Delta₁₂.f (p + q) ≫ linearYonedaPairingDesc C mu₁₂ p q phi psi) chi]
      _ = (c ≫ Deltaₗ).f (p + (q + r)) ≫
          (tensorHom Delta₁₂ (𝟙 K₃)).f (p + (q + r)) ≫
            linearYonedaPairingDescOfEq C muₗ (p + q) r (p + (q + r))
              (Nat.add_assoc p q r)
              (linearYonedaPairingDesc C mu₁₂ p q phi psi) chi ≫ a := by
        rw [linearYonedaPairingDescOfEq_naturality_assoc,
          HomologicalComplex.id_f, Category.id_comp]
      _ = (c ≫ Deltaₗ).f (p + (q + r)) ≫
          (tensorHom Delta₁₂ (𝟙 K₃)).f (p + (q + r)) ≫
            (HomologicalComplex.associator K₁ K₂ K₃).hom.f (p + (q + r)) ≫
              linearYonedaPairingDescOfEq C muᵣ p (q + r) (p + (q + r)) rfl phi
                (linearYonedaPairingDesc C mu₂₃ q r psi chi) := by
        rw [linearYonedaPairingDesc_assoc C mu₁₂ muₗ mu₂₃ muᵣ a hmu
          p q r (p + (q + r)) (Nat.add_assoc p q r) rfl phi psi chi]
      _ = Deltaᵣ.f (p + (q + r)) ≫
          (tensorHom (𝟙 K₁) Delta₂₃).f (p + (q + r)) ≫
            linearYonedaPairingDescOfEq C muᵣ p (q + r) (p + (q + r)) rfl phi
              (linearYonedaPairingDesc C mu₂₃ q r psi chi) := by
        simpa only [HomologicalComplex.comp_f, Category.assoc] using
          congrArg
            (fun F : Kᵣ.X (p + (q + r)) ⟶
                (tensorObj K₁ (tensorObj K₂ K₃)).X (p + (q + r)) =>
              F ≫ linearYonedaPairingDescOfEq C muᵣ p (q + r) (p + (q + r)) rfl
                phi (linearYonedaPairingDesc C mu₂₃ q r psi chi)) hDeltaN
      _ = _ := by
        rw [linearYonedaPairingDescOfEq_naturality]
        simp only [HomologicalComplex.id_f, Category.id_comp, linearYonedaPairingDesc]
  change
    ((((linearHomCochainComplexFunctor R C Mᵣ).obj (op Kᵣ)).XIsoOfEq
        (Nat.add_assoc p q r)).hom).hom
      (((linearYonedaCochainComparison R C c a).f ((p + q) + r)).hom
        (Deltaₗ.f ((p + q) + r) ≫
          linearYonedaPairingDesc C muₗ (p + q) r
            (Delta₁₂.f (p + q) ≫ linearYonedaPairingDesc C mu₁₂ p q phi psi) chi)) =
    Deltaᵣ.f (p + (q + r)) ≫
      linearYonedaPairingDesc C muᵣ p (q + r) phi
        (Delta₂₃.f (q + r) ≫ linearYonedaPairingDesc C mu₂₃ q r psi chi)
  erw [linearYonedaCochainComparison_f_apply R C c a ((p + q) + r)]
  erw [linearYonedaCochainComplex_XIsoOfEq_hom_apply R C Kᵣ Mᵣ
    (Nat.add_assoc p q r)]
  simpa only [Category.assoc] using hpair

end HomologicalComplex
