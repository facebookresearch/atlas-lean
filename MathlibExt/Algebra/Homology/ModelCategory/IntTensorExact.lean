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
# Exact integer cochain tensor under global coefficient projectivity

Let R be a commutative ring in universe u and assume every module object in ModuleCat_u(R) is
projective. Coefficient short exact sequences split, so additive coefficient tensor functors
preserve finite limits. Use the full convolution monoidal structure on integer cochain
complexes, with its graded coproduct, zero-object, triple-compatibility, and
fourfold-extensionality conditions.

The discrete antidiagonal coproduct functor is exact by module coproduct exactness. Combining it
with the exact coefficient pieces shows that K⊗(-) and (-)⊗K preserve finite limits for every
ℤ-indexed complex K. Hence tensoring monic cochain maps gives a monic tensor map, and every
nonnegative tensor-power map of a monic cochain map is monic.
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

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Assume every object of
ModuleCat_u(R) is projective. For K and n∈ℤ, P^L_{K,n}:L↦(K^p⊗L^q)_{p+q=n} preserves finite
limits. Each component is an exact cochain evaluation followed by an additive coefficient tensor
functor on the projective coefficient category. -/
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

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Assume every object of
ModuleCat_u(R) is projective. For K and n∈ℤ, P^R_{K,n}:L↦(L^p⊗K^q)_{p+q=n} preserves finite
limits. Component exactness follows from splitting of coefficient short exact rows and degree
evaluation. -/
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

/-- Let R be a commutative ring in universe u and use R-module carriers in u. For n∈ℤ, let
I_n={(p,q) | p+q=n}. The colimit functor from discrete I_n-diagrams of R-modules to R-modules,
namely their full coproduct, preserves finite limits. This is the AB4 exactness of module
coproducts. -/
instance intTensorDegreeColimit_preservesFiniteLimits (n : ℤ) :
    PreservesFiniteLimits
      (colim : (Discrete (intTensorTotalFiber n) ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
  inferInstance

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Assume every object of
ModuleCat_u(R) is projective. For every ℤ-indexed cochain complex K, K⊗(-) preserves finite
limits. Degree evaluation identifies it with the exact full coproduct of its left tensor pieces. -/
instance tensorLeftInt_preservesFiniteLimits (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesFiniteLimits (tensorLeft K) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    apply preservesLimitsOfShape_of_natIso (tensorLeftIntEvalIso K n).symm

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Assume every object of
ModuleCat_u(R) is projective. For every ℤ-indexed cochain complex K, (-)⊗K preserves finite
limits. Its degree-n pieces are L^p⊗K^q for every p+q=n. -/
instance tensorRightInt_preservesFiniteLimits (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesFiniteLimits (tensorRight K) where
  preservesFiniteLimits J [SmallCategory J] [FinCategory J] := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro n
    apply preservesLimitsOfShape_of_natIso (tensorRightIntEvalIso K n).symm

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Assume every object of
ModuleCat_u(R) is projective. For cochain maps f:K₁→K₂ and g:L₁→L₂ that are mono, the map
f⊗g:K₁⊗L₁→K₂⊗L₂ is mono. It factors as f⊗id_{L₁} followed by id_{K₂}⊗g, each preserved by the
finite-limit-preserving tensor functors. -/
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

/-- Let R be a commutative ring in universe u and use R-module carriers in u. Use the ℤ-indexed
cochain convolution tensor: all antidiagonal coproducts exist, coefficient tensoring preserves
zero objects in both variables and commutes with the coproducts in both triple
parenthesizations, and fourfold tensor inclusions determine maps. Assume every object of
ModuleCat_u(R) is projective. For a monic map f:K→L of ℤ-indexed cochain complexes and n∈ℕ, the
map f^{⊗n}:K^{⊗n}→L^{⊗n} is mono. Tensor powers start at the tensor unit when n=0 and advance by
tensoring the preceding power map with f. -/
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
