/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Monoidal

/-!
# Summand formulas for tensor maps and unitors of complexes

Let C be preadditive and monoidal with a zero object and bilinear tensor product, and let c be a
complex shape with tensor signs on an additive commutative monoid. A tensor map restricts on the
bidegree-(i,j) summand to the tensor of its degree-i and degree-j components. The tensor unit
complex is concentrated in degree zero. If the corresponding tensor functors preserve the zero
object, the left or right unitor of a complex restricts on the (0,i) or (i,0) summand to the
respective unitor of C after the degree-zero single-complex identification.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {I : Type w} [AddCommMonoid I] [DecidableEq I]
  {c : ComplexShape I} [c.TensorSigns]

omit [HasZeroObject C] in
@[reassoc]
theorem ιTensorObj_tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [HasTensor K₁ K₂] [HasTensor L₁ L₂]
    (i j n : I) (h : i + j = n) :
    ιTensorObj K₁ K₂ i j n h ≫ (tensorHom f g).f n =
      (f.f i ⊗ₘ g.f j) ≫ ιTensorObj L₁ L₂ i j n h := by
  rw [ι_mapBifunctorMap]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  change (f.f i ▷ K₂.X j) ≫ (L₁.X i ◁ g.f j) ≫
      ιTensorObj L₁ L₂ i j n h = _
  rfl

section Left

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

@[reassoc]
theorem ιTensorObj_leftUnitor_hom (K : HomologicalComplex C c) (i : I) :
    ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) ≫
        (leftUnitor K).hom.f i =
      ((singleObjXSelf c 0 (𝟙_ C)).hom ▷ K.X i) ≫ (λ_ (K.X i)).hom := by
  change ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) ≫
      (leftUnitor' K).hom i = _
  rw [← cancel_epi ((λ_ (K.X i)).inv ≫
    ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ K.X i))]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [← leftUnitor'_inv]
  change (leftUnitor' K).inv i ≫ (leftUnitor' K).hom i = _
  have hIso : (leftUnitor' K).inv i ≫ (leftUnitor' K).hom i = 𝟙 _ := by
    change (((leftUnitor' K).inv ≫ (leftUnitor' K).hom) :
      K.X ⟶ K.X) i = (𝟙 K.X) i
    exact congrFun (Iso.inv_hom_id (leftUnitor' K)) i
  rw [hIso]
  simp

end Left

section Right

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

@[reassoc]
theorem ιTensorObj_rightUnitor_hom (K : HomologicalComplex C c) (i : I) :
    ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) ≫
        (rightUnitor K).hom.f i =
      (K.X i ◁ (singleObjXSelf c 0 (𝟙_ C)).hom) ≫ (ρ_ (K.X i)).hom := by
  change ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) ≫
      (rightUnitor' K).hom i = _
  rw [← cancel_epi ((ρ_ (K.X i)).inv ≫
    (K.X i ◁ (singleObjXSelf c 0 (𝟙_ C)).inv))]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [← rightUnitor'_inv]
  change (rightUnitor' K).inv i ≫ (rightUnitor' K).hom i = _
  have hIso : (rightUnitor' K).inv i ≫ (rightUnitor' K).hom i = 𝟙 _ := by
    change (((rightUnitor' K).inv ≫ (rightUnitor' K).hom) :
      K.X ⟶ K.X) i = (𝟙 K.X) i
    exact congrFun (Iso.inv_hom_id (rightUnitor' K)) i
  rw [hIso]
  simp

end Right

end HomologicalComplex
