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
# Triple tensor products of homological complexes

This file records the homogeneous inclusions, extensionality principles,
naturality formulas, and associator formula for triple tensor products.
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

/-- The tridegree inclusion into the left-associated tensor product of complexes. -/
noncomputable abbrev ιTensorObj₃Left
    [HasTensor K₁ K₂] [HasTensor (tensorObj K₁ K₂) K₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (K₁.X i₁ ⊗ K₂.X i₂) ⊗ K₃.X i₃ ⟶
      (tensorObj (tensorObj K₁ K₂) K₃).X j :=
  mapBifunctor₁₂.ι (curriedTensor C) (curriedTensor C)
    K₁ K₂ K₃ c c i₁ i₂ i₃ j h

/-- The tridegree inclusion into the right-associated tensor product of complexes. -/
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

/-- Right-associated inclusion commutes with the inverse associator. -/
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
