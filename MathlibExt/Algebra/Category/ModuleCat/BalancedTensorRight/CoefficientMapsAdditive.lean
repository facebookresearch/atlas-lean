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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientMaps
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Universe
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import Mathlib.Algebra.Module.Bimodule

/-!
# Additive actual enriched coefficient transformations

These common-world foundation laws use the original quotient representatives.
They apply to independent-carrier facade coefficients after genuine lifting.
Neither R nor S is commutative. Arbitrary S-smul on S-linear maps is not claimed.
The revision-specific scoped Native checks are recorded in the integration plan;
current hosted PR build and review remain separate requirements.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe r s v
namespace ModuleCat.BalancedTensorRight
variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B B' : Type v) [AddCommGroup B] [AddCommGroup B']
  [Module R B] [Module R B'] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B']

/-- The zero coefficient map gives the actual zero tensor transformation. -/
theorem tensorCoefficientTransformation_zero :
    tensorCoefficientTransformation R S B B' (0 : B →ₗ[R] B')
      (by intro t x; simp) = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R X B
  intro x y
  change (tensorCoefficientMap R S B B' (0 : B →ₗ[R] B')
    (by intro t y; simp) X).hom (TensorProduct.Balanced.mk ℤ R X B x y) = 0
  rw [tensorCoefficientMap_mk, LinearMap.zero_apply]
  exact map_zero (TensorProduct.Balanced.mk ℤ R X B' x)

/-- Addition is addition on the original coefficient representatives. -/
theorem tensorCoefficientTransformation_add (f g : B →ₗ[R] B')
    (hf : ∀ (t : Sᵐᵒᵖ) (x : B), f (t • x) = t • f x)
    (hg : ∀ (t : Sᵐᵒᵖ) (x : B), g (t • x) = t • g x) :
    tensorCoefficientTransformation R S B B' (f + g)
        (by intro t x; simp only [LinearMap.add_apply, hf, hg, smul_add]) =
      tensorCoefficientTransformation R S B B' f hf +
        tensorCoefficientTransformation R S B B' g hg := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R X B
  intro x y
  change (tensorCoefficientMap R S B B' (f + g)
      (by intro t x; simp only [LinearMap.add_apply, hf, hg, smul_add]) X).hom
      (TensorProduct.Balanced.mk ℤ R X B x y) =
    (tensorCoefficientMap R S B B' f hf X).hom (TensorProduct.Balanced.mk ℤ R X B x y) +
      (tensorCoefficientMap R S B B' g hg X).hom (TensorProduct.Balanced.mk ℤ R X B x y)
  rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk,
    LinearMap.add_apply]
  exact map_add (TensorProduct.Balanced.mk ℤ R X B' x) _ _

/-- Original R-linear maps commuting with the actual outer action form an additive group. -/
def coefficientMapGroup : AddSubgroup (B →ₗ[R] B') where
  carrier f := ∀ (t : Sᵐᵒᵖ) (x : B), f (t • x) = t • f x
  zero_mem' := by
    intro t x
    simp only [LinearMap.zero_apply, smul_zero]
  add_mem' := by
    intro f g hf hg t x
    simp only [LinearMap.add_apply, hf t x, hg t x, smul_add]
  neg_mem' := by
    intro f hf t x
    simp only [LinearMap.neg_apply, hf t x, smul_neg]

/-- The actual coefficient construction is additive on the original bimodule morphisms. -/
def tensorCoefficientTransformationAddHom :
    coefficientMapGroup R S B B' →+
      (tensorFunctor R S B ⟶ tensorFunctor R S B') where
  toFun f := tensorCoefficientTransformation R S B B' f.val f.property
  map_zero' := tensorCoefficientTransformation_zero R S B B'
  map_add' f g := tensorCoefficientTransformation_add R S B B'
    f.val g.val f.property g.property

/-- The additive package retains the existing coefficient natural transformation. -/
theorem tensorCoefficientTransformationAddHom_apply
    (f : coefficientMapGroup R S B B') :
    tensorCoefficientTransformationAddHom R S B B' f =
      tensorCoefficientTransformation R S B B' f.val f.property := rfl

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Native derivation sends the actual zero tensor transformation to zero. -/
theorem torCoefficientTransformation_zero (n : ℕ) :
    torCoefficientTransformation R S B B' (0 : B →ₗ[R] B')
      (by intro t x; simp) n = 0 := by
  rw [torCoefficientTransformation, tensorCoefficientTransformation_zero,
    NatTrans.leftDerived_zero]
  rfl

/-- Native derived addition applies to the same actual coefficient transformations. -/
theorem torCoefficientTransformation_add (f g : B →ₗ[R] B')
    (hf : ∀ (t : Sᵐᵒᵖ) (x : B), f (t • x) = t • f x)
    (hg : ∀ (t : Sᵐᵒᵖ) (x : B), g (t • x) = t • g x) (n : ℕ) :
    torCoefficientTransformation R S B B' (f + g)
        (by intro t x; simp only [LinearMap.add_apply, hf, hg, smul_add]) n =
      torCoefficientTransformation R S B B' f hf n +
        torCoefficientTransformation R S B B' g hg n := by
  rw [torCoefficientTransformation, tensorCoefficientTransformation_add,
    NatTrans.leftDerived_add]
  rfl

/-- Native derivation is additive on the same original coefficient-map group. -/
def torCoefficientTransformationAddHom (n : ℕ) :
    coefficientMapGroup R S B B' →+
      (torFunctor R S B n ⟶ torFunctor R S B' n) where
  toFun f := torCoefficientTransformation R S B B' f.val f.property n
  map_zero' := torCoefficientTransformation_zero R S B B' n
  map_add' f g := torCoefficientTransformation_add R S B B'
    f.val g.val f.property g.property n

/-- The native additive package keeps the actual derived coefficient morphism. -/
theorem torCoefficientTransformationAddHom_apply
    (n : ℕ) (f : coefficientMapGroup R S B B') :
    torCoefficientTransformationAddHom R S B B' n f =
      torCoefficientTransformation R S B B' f.val f.property n := rfl

end Tor

section NativeCoefficientCategory

open scoped TensorProduct

/-- Native coefficients are modules over the actual two-factor scalar ring. -/
abbrev coefficientCategory := ModuleCat.{v} (R ⊗[ℤ] Sᵐᵒᵖ)

/-- Restrict the stored scalar action along the native left tensor inclusion. -/
def coefficientLeftModule (X : coefficientCategory R S) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Sᵐᵒᵖ)

/-- Restrict the same stored action along the native right tensor inclusion. -/
def coefficientRightModule (X : coefficientCategory R S) : Module Sᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Sᵐᵒᵖ).toRingHom

/-- The actual two restricted endpoint actions commute in their original order. -/
theorem coefficientActionsCommute (X : coefficientCategory R S) :
    letI := coefficientLeftModule R S X
    letI := coefficientRightModule R S X
    SMulCommClass R Sᵐᵒᵖ X := by
  let := coefficientLeftModule R S X
  let := coefficientRightModule R S X
  refine ⟨?_⟩
  intro r s x
  change (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • (((1 : R) ⊗ₜ[ℤ] s) • x) =
    ((1 : R) ⊗ₜ[ℤ] s) • ((r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • x)
  rw [← mul_smul, ← mul_smul]
  apply congrArg (fun z : R ⊗[ℤ] Sᵐᵒᵖ => z • x)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The native coefficient object gives an actual additive tensor functor. -/
def coefficientTensorObj (X : coefficientCategory R S) :
    ModuleCat.{v} Rᵐᵒᵖ ⥤+ ModuleCat.{v} Sᵐᵒᵖ := by
  letI := coefficientLeftModule R S X
  letI := coefficientRightModule R S X
  letI := coefficientActionsCommute R S X
  exact AdditiveFunctor.of (tensorFunctor R S X)

/-- A native coefficient morphism is linear for the restricted left action. -/
def coefficientLeftMap {X Y : coefficientCategory R S} (f : X ⟶ Y) :
    letI := coefficientLeftModule R S X
    letI := coefficientLeftModule R S Y
    X →ₗ[R] Y := by
  letI := coefficientLeftModule R S X
  letI := coefficientLeftModule R S Y
  refine { toFun := f.hom, map_add' := f.hom.map_add, map_smul' := ?_ }
  intro r x
  change f.hom ((r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • x) =
    (r ⊗ₜ[ℤ] (1 : Sᵐᵒᵖ)) • f.hom x
  exact f.hom.map_smul _ x

/-- The same native morphism also retains the actual right endpoint action. -/
theorem coefficientLeftMap_outer {X Y : coefficientCategory R S}
    (f : X ⟶ Y) (s : Sᵐᵒᵖ) (x : X) :
    letI := coefficientLeftModule R S X
    letI := coefficientLeftModule R S Y
    letI := coefficientRightModule R S X
    letI := coefficientRightModule R S Y
    coefficientLeftMap R S f (s • x) = s • coefficientLeftMap R S f x := by
  let := coefficientLeftModule R S X
  let := coefficientLeftModule R S Y
  let := coefficientRightModule R S X
  let := coefficientRightModule R S Y
  change f.hom (((1 : R) ⊗ₜ[ℤ] s) • x) =
    ((1 : R) ⊗ₜ[ℤ] s) • f.hom x
  exact f.hom.map_smul _ x

/-- Actual native bimodule morphisms give the original tensor coefficient maps. -/
def coefficientTensorTransformation {X Y : coefficientCategory R S} (f : X ⟶ Y) :
    (coefficientTensorObj R S X).obj ⟶ (coefficientTensorObj R S Y).obj := by
  letI := coefficientLeftModule R S X
  letI := coefficientRightModule R S X
  letI := coefficientActionsCommute R S X
  letI := coefficientLeftModule R S Y
  letI := coefficientRightModule R S Y
  letI := coefficientActionsCommute R S Y
  exact tensorCoefficientTransformation R S X Y
    (coefficientLeftMap R S f) (coefficientLeftMap_outer R S f)

/-- The native coefficient functor retains both actions rather than storing a desired square. -/
def coefficientTensorFunctor :
    coefficientCategory R S ⥤
      (ModuleCat.{v} Rᵐᵒᵖ ⥤+ ModuleCat.{v} Sᵐᵒᵖ) where
  obj := coefficientTensorObj R S
  map f := ObjectProperty.homMk (coefficientTensorTransformation R S f)
  map_id X := by
    let := coefficientLeftModule R S X
    let := coefficientRightModule R S X
    let := coefficientActionsCommute R S X
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext A
    let := TensorProduct.Balanced.rightModule ℤ R S A X
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R A X
    intro a x
    change (tensorCoefficientMap R S X X (coefficientLeftMap R S (𝟙 X))
        (coefficientLeftMap_outer R S (𝟙 X)) A).hom
      (TensorProduct.Balanced.mk ℤ R A X a x) =
        TensorProduct.Balanced.mk ℤ R A X a x
    rw [tensorCoefficientMap_mk]
    rfl
  map_comp {X Y Z} f g := by
    let := coefficientLeftModule R S X
    let := coefficientRightModule R S X
    let := coefficientActionsCommute R S X
    let := coefficientLeftModule R S Y
    let := coefficientRightModule R S Y
    let := coefficientActionsCommute R S Y
    let := coefficientLeftModule R S Z
    let := coefficientRightModule R S Z
    let := coefficientActionsCommute R S Z
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext A
    let := TensorProduct.Balanced.rightModule ℤ R S A X
    let := TensorProduct.Balanced.rightModule ℤ R S A Z
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply TensorProduct.Balanced.addHom_ext ℤ R A X
    intro a x
    change (tensorCoefficientMap R S X Z (coefficientLeftMap R S (f ≫ g))
        (coefficientLeftMap_outer R S (f ≫ g)) A).hom
      (TensorProduct.Balanced.mk ℤ R A X a x) =
      (tensorCoefficientMap R S Y Z (coefficientLeftMap R S g)
        (coefficientLeftMap_outer R S g) A).hom
        ((tensorCoefficientMap R S X Y (coefficientLeftMap R S f)
          (coefficientLeftMap_outer R S f) A).hom
          (TensorProduct.Balanced.mk ℤ R A X a x))
    rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk]
    rfl

/-- The actual coefficient functor is additive without any commutativity of S. -/
theorem coefficientTensorFunctor_additive : (coefficientTensorFunctor R S).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  let := coefficientLeftModule R S X
  let := coefficientRightModule R S X
  let := coefficientActionsCommute R S X
  let := coefficientLeftModule R S Y
  let := coefficientRightModule R S Y
  let := coefficientActionsCommute R S Y
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext A
  let := TensorProduct.Balanced.rightModule ℤ R S A X
  let := TensorProduct.Balanced.rightModule ℤ R S A Y
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A X
  intro a x
  change (tensorCoefficientMap R S X Y (coefficientLeftMap R S (f + g))
      (coefficientLeftMap_outer R S (f + g)) A).hom
    (TensorProduct.Balanced.mk ℤ R A X a x) =
    (tensorCoefficientMap R S X Y (coefficientLeftMap R S f)
      (coefficientLeftMap_outer R S f) A).hom
        (TensorProduct.Balanced.mk ℤ R A X a x) +
    (tensorCoefficientMap R S X Y (coefficientLeftMap R S g)
      (coefficientLeftMap_outer R S g) A).hom
        (TensorProduct.Balanced.mk ℤ R A X a x)
  rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk]
  change TensorProduct.Balanced.mk ℤ R A Y a (f.hom x + g.hom x) = _
  exact (TensorProduct.Balanced.mk ℤ R A Y a).map_add _ _

/-- Bundle the earned coefficient additivity using the native additive-functor category. -/
def coefficientTensorAdditiveFunctor :
    coefficientCategory R S ⥤+
      (ModuleCat.{v} Rᵐᵒᵖ ⥤+ ModuleCat.{v} Sᵐᵒᵖ) := by
  letI := coefficientTensorFunctor_additive R S
  exact AdditiveFunctor.of (coefficientTensorFunctor R S)

/-- Native degree derivation assembles the honest coefficient Tor functor. -/
def coefficientTorFunctor [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)] (n : ℕ) :
    coefficientCategory R S ⥤ (ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} Sᵐᵒᵖ) :=
  coefficientTensorFunctor R S ⋙
    CategoryTheory.leftDerivedDegreeFunctor
      (ModuleCat.{v} Rᵐᵒᵖ) (ModuleCat.{v} Sᵐᵒᵖ) n

end NativeCoefficientCategory

section OriginalActions

open scoped TensorProduct

/-- The original commuting actions package a native tensor-ring module, not a new bimodule engine. -/
def coefficientObjectOfActions : coefficientCategory R S := by
  letI : Module (R ⊗[ℤ] Sᵐᵒᵖ) B := TensorProduct.Algebra.module
  exact ModuleCat.of (R ⊗[ℤ] Sᵐᵒᵖ) B

/-- Restricting the native package recovers the given original left action. -/
theorem coefficientObjectOfActions_left (r : R) (x : B) :
    (coefficientLeftModule R S (coefficientObjectOfActions R S B)).smul r x =
      r • x := by
  change r • ((1 : Sᵐᵒᵖ) • x) = r • x
  rw [one_smul]

/-- The right restriction likewise recovers the original right S action. -/
theorem coefficientObjectOfActions_right (s : Sᵐᵒᵖ) (x : B) :
    (coefficientRightModule R S (coefficientObjectOfActions R S B)).smul s x =
      s • x := by
  change (1 : R) • (s • x) = s • x
  rw [one_smul]

/-- An actual original bimodule morphism is native-linear for the earned tensor-ring action. -/
def coefficientMapOfActions (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    coefficientObjectOfActions R S B ⟶ coefficientObjectOfActions R S B' := by
  letI : Module (R ⊗[ℤ] Sᵐᵒᵖ) B := TensorProduct.Algebra.module
  letI : Module (R ⊗[ℤ] Sᵐᵒᵖ) B' := TensorProduct.Algebra.module
  refine ModuleCat.ofHom
    { toFun := f
      map_add' := f.map_add
      map_smul' := ?_ }
  intro z x
  induction z using TensorProduct.inductionOn with
  | tmul r s =>
    change f (r • (s • x)) = r • (s • f x)
    rw [f.map_smul, hf]
  | add z w hz hw =>
    change f ((z + w) • x) = (z + w) • f x
    rw [add_smul, add_smul, f.map_add, hz, hw]
    rfl

/-- The native coefficient morphism evaluates to the original raw map. -/
theorem coefficientMapOfActions_apply (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (x : B) :
    (coefficientMapOfActions R S B B' f hf).hom x = f x := rfl

end OriginalActions

end ModuleCat.BalancedTensorRight
