/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.ModelCategory.IntMonoidalPreservesColimits
public import MathlibExt.CategoryTheory.Preadditive.SemisimpleExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.AB
public import MathlibExt.RingTheory.DifferentialGraded.TensorPowers

/-!
# Exactness of the actual full integer tensor on all-projective coefficients

Actual coefficient short exact sequences split and their tensor images stay
split. The original degree-piece coproducts are exact by native module AB4.
Every actual full integer tensor functor therefore preserves finite limits;
Field vector spaces instantiate the original coefficient condition.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]
variable [∀ X Y : GradedObject ℤ (ModuleCat.{u} R), GradedObject.HasTensor X Y]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).obj X)]
variable [∀ X : ModuleCat.{u} R,
  PreservesColimit (Functor.empty.{0} (ModuleCat.{u} R))
    ((curriedTensor (ModuleCat.{u} R)).flip.obj X)]
variable [∀ W X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasTensor₄ObjExt W X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ (ModuleCat.{u} R),
  GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ M : ModuleCat.{u} R, Projective M]

/-- Native coefficient splitting proves finite-limit preservation of every actual left tensor
piece. -/
instance tensorLeftIntDegreePieces_preservesFiniteLimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesFiniteLimits (tensorLeftIntDegreePieces K n) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply preservesLimitsOfShape_of_evaluation _ J
    intro i
    let F : ModuleCat.{u} R ⥤ ModuleCat.{u} R := tensorLeft (K.X i.as.val.1)
    let : PreservesFiniteLimits F := additive_preservesFiniteLimits_of_allProjective F
    change PreservesLimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.2 ⋙ F)
    infer_instance

/-- Native coefficient splitting proves finite-limit preservation of every actual right tensor
piece. -/
instance tensorRightIntDegreePieces_preservesFiniteLimits
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    PreservesFiniteLimits (tensorRightIntDegreePieces K n) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply preservesLimitsOfShape_of_evaluation _ J
    intro i
    let F : ModuleCat.{u} R ⥤ ModuleCat.{u} R := tensorRight (K.X i.as.val.2)
    let : PreservesFiniteLimits F := additive_preservesFiniteLimits_of_allProjective F
    change PreservesLimitsOfShape J
      (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i.as.val.1 ⋙ F)
    infer_instance

/-- The original module coproduct in every integer degree is exact by native AB4. -/
instance intTensorDegreeColimit_preservesFiniteLimits (n : ℤ) :
    PreservesFiniteLimits
      (colim : (Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
  inferInstance

/-- The actual full integer left tensor functor preserves finite limits in the genuine
coefficient domain. -/
instance tensorLeftInt_preservesFiniteLimits (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesFiniteLimits (tensorLeft K) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    apply preservesLimitsOfShape_of_natIso (tensorLeftIntEvalIso K n).symm

/-- The actual full integer right tensor functor preserves finite limits in the same coefficient
domain. -/
instance tensorRightInt_preservesFiniteLimits (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesFiniteLimits (tensorRight K) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    apply preservesLimitsOfShape_of_natIso (tensorRightIntEvalIso K n).symm

/-- Actual tensoring of two arbitrary monic chain maps stays monic in this coefficient domain. -/
lemma tensorHom_mono_of_allProjective
    {K₁ K₂ L₁ L₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) [Mono f] [Mono g] :
    Mono (HomologicalComplex.tensorHom f g) := by
  let : Mono (HomologicalComplex.tensorHom f (𝟙 L₁)) :=
    inferInstanceAs (Mono ((tensorRight L₁).map f))
  let : Mono (HomologicalComplex.tensorHom (𝟙 K₂) g) :=
    inferInstanceAs (Mono ((tensorLeft K₂).map g))
  have h : HomologicalComplex.tensorHom f (𝟙 L₁) ≫
      HomologicalComplex.tensorHom (𝟙 K₂) g = HomologicalComplex.tensorHom f g := by
    rw [HomologicalComplex.tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  rw [← h]
  exact mono_comp _ _

/-- Every actual tensor-power map of an arbitrary monic chain map is monic. -/
lemma tensorPowMap_mono_of_allProjective
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [Mono f] (n : ℕ) :
    Mono (tensorPowMap f n) := by
  induction n with
  | zero => change Mono (𝟙 _); infer_instance
  | succ n ih =>
    let : Mono (tensorPowMap f n) := ih
    change Mono (HomologicalComplex.tensorHom (tensorPowMap f n) f)
    exact tensorHom_mono_of_allProjective _ _

end CochainComplex
