/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.TensorUnitor

/-!
# Homogeneous inclusions and associators for triple tensor complexes

Let C be a preadditive monoidal category whose tensor functor is additive
in both variables. Let I be an additive monoid with decidable equality,
c a complex shape on I with compatible tensor signs, and K₁,K₂,K₃
complexes of shape c.

When the component coproducts defining the indicated tensor products
exist, a tridegree (i₁,i₂,i₃) with i₁+i₂+i₃ = j gives inclusions
(K₁_(i₁) ⊗ K₂_(i₂)) ⊗ K₃_(i₃) → ((K₁⊗K₂)⊗K₃)_j
and K₁_(i₁) ⊗ (K₂_(i₂) ⊗ K₃_(i₃)) → (K₁⊗(K₂⊗K₃))_j.
These inclusions factor through the corresponding binary inclusions
and are natural for maps of all three complexes.

For the associator, assume both tensor parenthesizations exist,
− ⊗ K₃_(i₃) preserves every coproduct of K₁_(i₁) ⊗ K₂_(i₂)
with i₁+i₂ fixed, and K₁_(i₁) ⊗ − preserves every coproduct of
K₂_(i₂) ⊗ K₃_(i₃) with i₂+i₃ fixed. On a tridegree inclusion the
complex associator is the associator of the three component objects;
the inverse satisfies the reverse equation. The category object,
morphism and degree-index universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]
  (K₁ K₂ K₃ : HomologicalComplex C c)

/-- In a preadditive monoidal category with tensor additive
in both variables, let K₁,K₂,K₃ have a common shape c with tensor
signs on an additive monoid I with decidable equality. If K₁⊗K₂ and (K₁⊗K₂)⊗K₃ exist,
then i₁+i₂+i₃ = j gives the component coproduct inclusion
(K₁_(i₁) ⊗ K₂_(i₂)) ⊗ K₃_(i₃) → ((K₁⊗K₂)⊗K₃)_j.
The required existence conditions concern the tensor coproducts in
each degree. -/
noncomputable abbrev ιTensorObj₃Left
    [HasTensor K₁ K₂] [HasTensor (tensorObj K₁ K₂) K₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (K₁.X i₁ ⊗ K₂.X i₂) ⊗ K₃.X i₃ ⟶
      (tensorObj (tensorObj K₁ K₂) K₃).X j :=
  mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C)
    K₁ K₂ K₃ c c i₁ i₂ i₃ j h

/-- In a preadditive monoidal category with tensor additive
in both variables, let K₁,K₂,K₃ have a common shape c with tensor
signs on an additive monoid I with decidable equality. If K₂⊗K₃ and K₁⊗(K₂⊗K₃) exist,
then i₁+i₂+i₃ = j gives the component coproduct inclusion
K₁_(i₁) ⊗ (K₂_(i₂) ⊗ K₃_(i₃)) → (K₁⊗(K₂⊗K₃))_j,
using associativity of addition to group i₂+i₃. -/
noncomputable abbrev ιTensorObj₃Right
    [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    K₁.X i₁ ⊗ (K₂.X i₂ ⊗ K₃.X i₃) ⟶
      (tensorObj K₁ (tensorObj K₂ K₃)).X j :=
  mapBifunctor₂₃.ι (curriedTensor C) (curriedTensor C)
    K₁ K₂ K₃ c c c i₁ i₂ i₃ j h

@[reassoc]
theorem ιTensorObj₃Left_eq
    [HasTensor K₁ K₂] [HasTensor (tensorObj K₁ K₂) K₃]
    (i₁ i₂ i₃ j i₁₂ : I) (h₁₂ : i₁ + i₂ = i₁₂)
    (h : i₁₂ + i₃ = j) :
    ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j (by rw [h₁₂, h]) =
      (ιTensorObj K₁ K₂ i₁ i₂ i₁₂ h₁₂ ▷ K₃.X i₃) ≫
        ιTensorObj (tensorObj K₁ K₂) K₃ i₁₂ i₃ j h := by
  exact mapBifunctor₁₂.ι_eq (curriedTensor C) (curriedTensor C)
    K₁ K₂ K₃ c c i₁ i₂ i₃ i₁₂ j h₁₂ h

@[reassoc]
theorem ιTensorObj₃Right_eq
    [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    (i₁ i₂ i₃ j i₂₃ : I) (h₂₃ : i₂ + i₃ = i₂₃)
    (h : i₁ + i₂₃ = j) :
    ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j
        (by rw [add_assoc, h₂₃, h]) =
      (K₁.X i₁ ◁ ιTensorObj K₂ K₃ i₂ i₃ i₂₃ h₂₃) ≫
        ιTensorObj K₁ (tensorObj K₂ K₃) i₁ i₂₃ j h := by
  exact mapBifunctor₂₃.ι_eq (curriedTensor C) (curriedTensor C)
    K₁ K₂ K₃ c c c i₁ i₂ i₃ i₂₃ j h₂₃ h

@[ext (iff := false)]
theorem tensorObj₃Left_hom_ext
    [HasTensor K₁ K₂] [HasTensor (tensorObj K₁ K₂) K₃]
    [HasGoodTensor₁₂ K₁ K₂ K₃]
    {j : I} {A : C} (f g : (tensorObj (tensorObj K₁ K₂) K₃).X j ⟶ A)
    (hfg : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j h ≫ f =
        ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j h ≫ g) :
    f = g := by
  exact mapBifunctor₁₂.hom_ext hfg

@[ext (iff := false)]
theorem tensorObj₃Right_hom_ext
    [HasTensor K₂ K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₂₃ K₁ K₂ K₃]
    {j : I} {A : C} (f g : (tensorObj K₁ (tensorObj K₂ K₃)).X j ⟶ A)
    (hfg : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j h ≫ f =
        ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j h ≫ g) :
    f = g := by
  exact mapBifunctor₂₃.hom_ext c hfg

@[reassoc (attr := simp)]
theorem ιTensorObj₃Left_tensorHom
    {L₁ L₂ L₃ : HomologicalComplex C c}
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X]
    [HasTensor (tensorObj K₁ K₂) K₃]
    [GradedObject.HasTensor L₁.X L₂.X]
    [GradedObject.HasTensor (GradedObject.Monoidal.tensorObj L₁.X L₂.X) L₃.X]
    [HasTensor (tensorObj L₁ L₂) L₃]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j h ≫
        (tensorHom (tensorHom f₁ f₂) f₃).f j =
      ((f₁.f i₁ ⊗ₘ f₂.f i₂) ⊗ₘ f₃.f i₃) ≫
        ιTensorObj₃Left L₁ L₂ L₃ i₁ i₂ i₃ j h := by
  exact GradedObject.Monoidal.ιTensorObj₃'_tensorHom
    (X₁ := K₁.X) (X₂ := K₂.X) (X₃ := K₃.X)
    (Y₁ := L₁.X) (Y₂ := L₂.X) (Y₃ := L₃.X)
    f₁.f f₂.f f₃.f i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
theorem ιTensorObj₃Right_tensorHom
    {L₁ L₂ L₃ : HomologicalComplex C c}
    [GradedObject.HasTensor K₂.X K₃.X]
    [GradedObject.HasTensor K₁.X (GradedObject.Monoidal.tensorObj K₂.X K₃.X)]
    [HasTensor K₁ (tensorObj K₂ K₃)]
    [GradedObject.HasTensor L₂.X L₃.X]
    [GradedObject.HasTensor L₁.X (GradedObject.Monoidal.tensorObj L₂.X L₃.X)]
    [HasTensor L₁ (tensorObj L₂ L₃)]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) (f₃ : K₃ ⟶ L₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j h ≫
        (tensorHom f₁ (tensorHom f₂ f₃)).f j =
      (f₁.f i₁ ⊗ₘ (f₂.f i₂ ⊗ₘ f₃.f i₃)) ≫
        ιTensorObj₃Right L₁ L₂ L₃ i₁ i₂ i₃ j h := by
  exact GradedObject.Monoidal.ιTensorObj₃_tensorHom
    (X₁ := K₁.X) (X₂ := K₂.X) (X₃ := K₃.X)
    (Y₁ := L₁.X) (Y₂ := L₂.X) (Y₃ := L₃.X)
    f₁.f f₂.f f₃.f i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
theorem ιTensorObj₃Left_associator_hom
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃]
    [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃]
    [HasGoodTensor₂₃ K₁ K₂ K₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j h ≫
        (associator K₁ K₂ K₃).hom.f j =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).hom ≫
        ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j h := by
  exact ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c i₁ i₂ i₃ j h

/-- For complexes K₁,K₂,K₃ in a preadditive monoidal category
with additive tensor, on an additive degree monoid with decidable equality
and a tensor-sign shape, assume both
parenthesizations exist. Assume also that tensoring by K₃_(i₃) on
the right preserves the K₁,K₂ degree coproducts and tensoring by
K₁_(i₁) on the left preserves the K₂,K₃ degree coproducts.
For i₁+i₂+i₃ = j, the inverse complex associator satisfies
α_K⁻¹ ∘ ι_R = ι_L ∘ α_(K₁_(i₁),K₂_(i₂),K₃_(i₃))⁻¹.
Both paths map the right-associated component tensor to the
degree-j left-associated tensor complex. -/
@[reassoc]
theorem ιTensorObj₃Right_associator_inv
    (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃]
    [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃]
    [HasGoodTensor₂₃ K₁ K₂ K₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃Right K₁ K₂ K₃ i₁ i₂ i₃ j h ≫
        (associator K₁ K₂ K₃).inv.f j =
      (α_ (K₁.X i₁) (K₂.X i₂) (K₃.X i₃)).inv ≫
        ιTensorObj₃Left K₁ K₂ K₃ i₁ i₂ i₃ j h := by
  have hInv : (associator K₁ K₂ K₃).inv.f j ≫
      (associator K₁ K₂ K₃).hom.f j = 𝟙 _ := by
    have hj := congrArg (fun f => f.f j) (associator K₁ K₂ K₃).inv_hom_id
    simpa only [comp_f, id_f] using hj
  have hLeft := ιTensorObj₃Left_associator_hom K₁ K₂ K₃ i₁ i₂ i₃ j h
  apply (cancel_mono ((associator K₁ K₂ K₃).hom.f j)).mp
  rw [Category.assoc, Category.assoc, hInv, Category.comp_id, hLeft,
    Iso.inv_hom_id_assoc]

end HomologicalComplex
