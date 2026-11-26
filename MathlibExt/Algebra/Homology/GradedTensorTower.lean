/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TripleTensor

/-!
# Graded coordinates of tensor products and associators

Let `C` be a monoidal category and let degrees form an additive monoid `I`. When the graded
tensor coproducts exist, the tensor object and tensor maps are determined by the graded
objects and maps of their factors. When the iterated tensor coproduct comparisons exist, the
associator has the corresponding graded components.

For homological complexes in a preadditive `C` with additive tensor functors, decidable
equality on `I`, and tensor signs for the complex shape, these graded formulas describe the
underlying tensor carrier, tensor-map components, and associator components. Equal graded
carriers and heterogeneously equal graded maps give heterogeneous equality of the
corresponding components. The formulas retain the given tensor-existence and iterated-
comparison hypotheses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject.Monoidal

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {I : Type w} [AddMonoid I]

/-- Congruence of graded tensor objects.

For graded objects `X, Y, X', Y'` whose tensor coproducts exist, equalities `X = X'` and `Y =
Y'` imply equality of their graded tensor objects. -/
theorem tensorObj_eq
    (X Y X' Y' : GradedObject I C)
    [HasTensor X Y] [HasTensor X' Y']
    (hX : X = X') (hY : Y = Y') : tensorObj X Y = tensorObj X' Y' := by
  subst hX
  subst hY
  rfl

/-- Heterogeneous congruence of a graded tensor-map component.

If the four endpoint graded objects of `f` and `g` equal those of `f'` and `g'`, and the
corresponding factor maps are heterogeneously equal, their tensor maps are heterogeneously
equal in every degree `j`. The source and target graded tensors are assumed to exist. -/
theorem tensorHom_apply_heq
    {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : GradedObject I C}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (f' : X₁' ⟶ X₂') (g' : Y₁' ⟶ Y₂')
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂]
    [HasTensor X₁' Y₁'] [HasTensor X₂' Y₂']
    (hX₁ : X₁ = X₁') (hX₂ : X₂ = X₂')
    (hY₁ : Y₁ = Y₁') (hY₂ : Y₂ = Y₂')
    (hf : HEq f f') (hg : HEq g g') (j : I) :
    HEq (tensorHom f g j) (tensorHom f' g' j) := by
  subst hX₁
  subst hX₂
  subst hY₁
  subst hY₂
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- Heterogeneous congruence of a graded associator component.

For two triples of equal graded objects, the forward associator components in degree `j` are
heterogeneously equal. The two sets of graded tensors and iterated tensor coproduct
comparisons are assumed to exist. -/
theorem associator_hom_apply_heq
    (X₁ X₂ X₃ X₁' X₂' X₃' : GradedObject I C)
    [HasTensor X₁ X₂] [HasTensor X₂ X₃]
    [HasTensor (tensorObj X₁ X₂) X₃]
    [HasTensor X₁ (tensorObj X₂ X₃)]
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasTensor X₁' X₂'] [HasTensor X₂' X₃']
    [HasTensor (tensorObj X₁' X₂') X₃']
    [HasTensor X₁' (tensorObj X₂' X₃')]
    [HasGoodTensor₁₂Tensor X₁' X₂' X₃']
    [HasGoodTensorTensor₂₃ X₁' X₂' X₃']
    (h₁ : X₁ = X₁') (h₂ : X₂ = X₂') (h₃ : X₃ = X₃') (j : I) :
    HEq ((associator X₁ X₂ X₃).hom j)
      ((associator X₁' X₂' X₃').hom j) := by
  subst X₁'
  subst X₂'
  subst X₃'
  rfl

end CategoryTheory.GradedObject.Monoidal

namespace HomologicalComplex

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {I : Type w} [AddMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]

/-- The graded carrier of a tensor product of complexes.

For complexes `K` and `L` with the required graded tensor coproducts, the carrier of their
tensor complex is the graded tensor of `K.X` and `L.X`. -/
theorem tensorObj_X_eq_graded
    (K L : HomologicalComplex C c) [GradedObject.HasTensor K.X L.X] :
    (tensorObj K L).X = GradedObject.Monoidal.tensorObj K.X L.X := rfl

/-- The graded component formula for a tensor map of complexes.

For chain maps `f` and `g`, the degree-`j` component of their tensor map is the graded tensor
map of their component families `f.f` and `g.f`, assuming the source and target graded tensors
exist. -/
theorem tensorHom_f_eq_graded
    {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor L₁.X L₂.X] (j : I) :
    (tensorHom f g).f j =
      GradedObject.Monoidal.tensorHom f.f g.f j := rfl

/-- The graded component formula for a complex associator.

For three complexes with the stated tensor and iterated-comparison hypotheses, the degree-`j`
component of the forward complex associator equals the associator component of their graded
carriers. -/
theorem associator_hom_f_eq_graded
    (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor K₂.X K₃.X]
    [GradedObject.HasTensor (tensorObj K₁ K₂).X K₃.X]
    [GradedObject.HasTensor K₁.X (tensorObj K₂ K₃).X]
    [GradedObject.HasTensor
      (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X]
    [GradedObject.HasTensor K₁.X
      (GradedObject.Monoidal.tensorObj K₂.X K₃.X)]
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
    [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]
    (j : I) :
    (associator K₁ K₂ K₃).hom.f j =
      (GradedObject.Monoidal.associator K₁.X K₂.X K₃.X).hom j := rfl

/-- Heterogeneous congruence of complex tensor-map components.

Equal source and target graded carriers together with heterogeneous equalities of the two
factor component families imply heterogeneous equality of the degree-`j` tensor-map
components. Both source and target tensor products are assumed to exist. -/
theorem tensorHom_f_heq
    {K₁ K₂ L₁ L₂ K₁' K₂' L₁' L₂' : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    (f' : K₁' ⟶ L₁') (g' : K₂' ⟶ L₂')
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor L₁.X L₂.X]
    [GradedObject.HasTensor K₁'.X K₂'.X]
    [GradedObject.HasTensor L₁'.X L₂'.X]
    (hK₁ : K₁.X = K₁'.X) (hL₁ : L₁.X = L₁'.X)
    (hK₂ : K₂.X = K₂'.X) (hL₂ : L₂.X = L₂'.X)
    (hf : HEq f.f f'.f) (hg : HEq g.f g'.f) (j : I) :
    HEq ((tensorHom f g).f j) ((tensorHom f' g').f j) := by
  rw [tensorHom_f_eq_graded, tensorHom_f_eq_graded]
  exact GradedObject.Monoidal.tensorHom_apply_heq
    f.f g.f f'.f g'.f hK₁ hL₁ hK₂ hL₂ hf hg j

/-- Heterogeneous congruence of complex associator components.

For triples of complexes with equal graded carriers, the forward associator components in
every degree `j` are heterogeneously equal, under the stated tensor-existence and iterated-
comparison hypotheses. -/
theorem associator_hom_f_heq
    (K₁ K₂ K₃ L₁ L₂ L₃ : HomologicalComplex C c)
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor K₂.X K₃.X]
    [GradedObject.HasTensor (tensorObj K₁ K₂).X K₃.X]
    [GradedObject.HasTensor K₁.X (tensorObj K₂ K₃).X]
    [GradedObject.HasTensor
      (GradedObject.Monoidal.tensorObj K₁.X K₂.X) K₃.X]
    [GradedObject.HasTensor K₁.X
      (GradedObject.Monoidal.tensorObj K₂.X K₃.X)]
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X]
    [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X]
    [GradedObject.HasTensor L₁.X L₂.X]
    [GradedObject.HasTensor L₂.X L₃.X]
    [GradedObject.HasTensor (tensorObj L₁ L₂).X L₃.X]
    [GradedObject.HasTensor L₁.X (tensorObj L₂ L₃).X]
    [GradedObject.HasTensor
      (GradedObject.Monoidal.tensorObj L₁.X L₂.X) L₃.X]
    [GradedObject.HasTensor L₁.X
      (GradedObject.Monoidal.tensorObj L₂.X L₃.X)]
    [GradedObject.HasGoodTensor₁₂Tensor L₁.X L₂.X L₃.X]
    [GradedObject.HasGoodTensorTensor₂₃ L₁.X L₂.X L₃.X]
    (h₁ : K₁.X = L₁.X) (h₂ : K₂.X = L₂.X) (h₃ : K₃.X = L₃.X)
    (j : I) :
    HEq ((associator K₁ K₂ K₃).hom.f j)
      ((associator L₁ L₂ L₃).hom.f j) := by
  rw [associator_hom_f_eq_graded, associator_hom_f_eq_graded]
  exact GradedObject.Monoidal.associator_hom_apply_heq
    K₁.X K₂.X K₃.X L₁.X L₂.X L₃.X h₁ h₂ h₃ j

end HomologicalComplex
