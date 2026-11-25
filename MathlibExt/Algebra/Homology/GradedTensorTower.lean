/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TripleTensor

/-!
# Graded component formulas for tensor towers

A component of a tensor map on homological complexes depends on the graded
maps of its factors. Likewise the associator component depends on the three
graded carriers. The formulas identify these components with the graded
object tensor and associator constructions.

Heterogeneous congruence lemmas compare different carrier presentations
using equalities of graded objects and heterogeneous equalities of their
maps. When endpoints agree, these yield ordinary equality of the complex
components. The component formulas do not depend on the differentials.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject.Monoidal

universe v u w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {I : Type w} [AddMonoid I]

/-- Congruence for a graded tensor object after substituting both carrier
equalities, including their dependent tensor-existence instances. -/
theorem tensorObj_eq
    (X Y X' Y' : GradedObject I C)
    [HasTensor X Y] [HasTensor X' Y']
    (hX : X = X') (hY : Y = Y') : tensorObj X Y = tensorObj X' Y' := by
  subst hX
  subst hY
  rfl

/-- Heterogeneous congruence for a graded tensor-map component.

Rewrite direction: after a complex tensor component has been rewritten to
`GradedObject.Monoidal.tensorHom`, use this lemma to replace the two input
graded maps by `HEq`-equal shallow maps without unfolding the tensor object.
`GradedTensorTowerTests` contains a direct heterogeneous client. -/
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

/-- Heterogeneous congruence for the hom of a graded associator at one degree.

Rewrite direction: replace the three carrier objects from left to right; the
result compares the associator components without reducing either nested
tensor tower.  `GradedTensorTowerTests` exercises all three replacements. -/
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

/-- The carrier of a complex tensor product is the graded tensor product.

Rewrite direction: from `(tensorObj K L).X` to
`GradedObject.Monoidal.tensorObj K.X L.X`.  Applying this once exposes one
tower layer; the contract test rewrites the carrier equality directly. -/
theorem tensorObj_X_eq_graded
    (K L : HomologicalComplex C c) [GradedObject.HasTensor K.X L.X] :
    (tensorObj K L).X = GradedObject.Monoidal.tensorObj K.X L.X := rfl

/-- A complex tensor-map component is the corresponding graded tensor map.

Rewrite direction: from `(tensorHom f g).f j` to the graded-object
`tensorHom` at `j`.  This is the one-level peeling rewrite used before
`GradedObject.Monoidal.tensorHom_apply_heq`; the test module pins that exact
two-step pattern. -/
theorem tensorHom_f_eq_graded
    {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [GradedObject.HasTensor K₁.X K₂.X]
    [GradedObject.HasTensor L₁.X L₂.X] (j : I) :
    (tensorHom f g).f j =
      GradedObject.Monoidal.tensorHom f.f g.f j := rfl

/-- A complex associator component is the graded-carrier associator component.

Rewrite direction: from `HomologicalComplex.associator … .hom.f j` to the
graded-object associator at `j`.  The contract test then changes carriers
with `GradedObject.Monoidal.associator_hom_apply_heq`. -/
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

/-- Nested tensor-map components are heterogeneously congruent when their two
leaf graded maps are heterogeneously equal.

Rewrite direction: this packages `tensorHom_f_eq_graded` on both sides and
reduces a nested complex-tower comparison to four shallow carrier equalities
plus the two shallow hypotheses `hf` and `hg`.  Abstract contract tests
use it under `eq_of_heq`; concrete Bar/Cobar clients additionally need
propositional leaf equalities. -/
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

/-- Complex associator components are heterogeneously congruent when the
three graded carriers are equal.

Rewrite direction: this packages `associator_hom_f_eq_graded` on both sides
and leaves only the shallow carrier equalities `h₁`, `h₂`, and `h₃`.
Abstract contract tests invoke the `HEq` form directly; recovering the
ordinary Bar/Cobar bridge needs propositional leaf equalities (see the
test module note). -/
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
