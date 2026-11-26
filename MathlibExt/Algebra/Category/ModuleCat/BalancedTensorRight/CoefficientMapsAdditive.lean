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
# Additive coefficient maps for bimodule tensor and Tor

For `R`-left, `S`-right bimodules `B` and `B'`, the `R`-linear maps that preserve the right
`S`-action form an additive subgroup. Sending such a map to its tensor natural transformation
is additive, and, when right `R`-modules have projective resolutions, the same holds for the
derived Tor transformations in each degree.

A module over `R ⊗[ℤ] Sᵐᵒᵖ` supplies commuting left `R`- and right `S`-actions by restricting
the two tensor-factor inclusions. This coefficient category maps additively to the category of
additive right-module tensor functors. Bimodules with given commuting actions, and maps
preserving them, define coefficient objects and morphisms with the same underlying values.

The rings may be noncommutative and have independent universes; coefficient and tensor-input
carriers share universe `v`.
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

/-- Zero coefficient induces the zero tensor transformation.

The natural transformation of right-module-valued tensor functors induced by the zero bimodule
coefficient map is zero. -/
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

/-- Tensor coefficient transformations preserve addition.

For `R`-linear coefficient maps `f` and `g` preserving the right `S`-action, the tensor
transformation for `f + g` is the sum of their tensor transformations. -/
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

/-- Additive subgroup of maps preserving both coefficient actions.

The subgroup of `B →ₗ[R] B'` consists of maps satisfying `f (t • x) = t • f x` for all `t :
Sᵐᵒᵖ` and `x : B`. It is closed under zero, addition, and negation. -/
def coefficientMapGroup : AddSubgroup (B →ₗ[R] B') where
  carrier := {f : B →ₗ[R] B' | ∀ (t : Sᵐᵒᵖ) (x : B), f (t • x) = t • f x}
  zero_mem' := by
    intro t x
    simp only [LinearMap.zero_apply, smul_zero]
  add_mem' := by
    intro f g hf hg t x
    simp only [LinearMap.add_apply, hf t x, hg t x, smul_add]
  neg_mem' := by
    intro f hf t x
    simp only [LinearMap.neg_apply, hf t x, smul_neg]

/-- Additive map from bimodule morphisms to tensor transformations.

The assignment sending a map in `coefficientMapGroup R S B B'` to its tensor coefficient
natural transformation is an additive group homomorphism. -/
def tensorCoefficientTransformationAddHom :
    coefficientMapGroup R S B B' →+
      (tensorFunctor R S B ⟶ tensorFunctor R S B') where
  toFun f := tensorCoefficientTransformation R S B B' f.val f.property
  map_zero' := tensorCoefficientTransformation_zero R S B B'
  map_add' f g := tensorCoefficientTransformation_add R S B B'
    f.val g.val f.property g.property

/-- Value of the additive tensor-transformation assignment.

For a compatible coefficient map `f`, the additive assignment returns
`tensorCoefficientTransformation R S B B' f.val f.property`. -/
theorem tensorCoefficientTransformationAddHom_apply
    (f : coefficientMapGroup R S B B') :
    tensorCoefficientTransformationAddHom R S B B' f =
      tensorCoefficientTransformation R S B B' f.val f.property := rfl

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Zero coefficient induces the zero Tor transformation.

Assuming projective resolutions for right `R`-modules, the degree-`n` derived coefficient
transformation induced by the zero map is zero. -/
theorem torCoefficientTransformation_zero (n : ℕ) :
    torCoefficientTransformation R S B B' (0 : B →ₗ[R] B')
      (by intro t x; simp) n = 0 := by
  rw [torCoefficientTransformation, tensorCoefficientTransformation_zero,
    NatTrans.leftDerived_zero]
  rfl

/-- Tor coefficient transformations preserve addition.

For compatible coefficient maps `f` and `g`, the degree-`n` Tor coefficient transformation of
`f + g` equals the sum of their degree-`n` transformations. -/
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

/-- Additive map from bimodule morphisms to Tor transformations.

In each natural degree `n`, compatible coefficient maps form an additive group mapping to the
additive group of natural transformations between their Tor functors. -/
def torCoefficientTransformationAddHom (n : ℕ) :
    coefficientMapGroup R S B B' →+
      (torFunctor R S B n ⟶ torFunctor R S B' n) where
  toFun f := torCoefficientTransformation R S B B' f.val f.property n
  map_zero' := torCoefficientTransformation_zero R S B B' n
  map_add' f g := torCoefficientTransformation_add R S B B'
    f.val g.val f.property g.property n

/-- Value of the additive Tor-transformation assignment.

For `f` in the compatible coefficient-map subgroup, the degree-`n` additive assignment returns
the Tor transformation induced by `f.val` and `f.property`. -/
theorem torCoefficientTransformationAddHom_apply
    (n : ℕ) (f : coefficientMapGroup R S B B') :
    torCoefficientTransformationAddHom R S B B' n f =
      torCoefficientTransformation R S B B' f.val f.property n := rfl

end Tor

section NativeCoefficientCategory

open scoped TensorProduct

/-- Module category realizing commuting coefficient actions.

The coefficient category is `ModuleCat.{v} (R ⊗[ℤ] Sᵐᵒᵖ)`. Restriction along the tensor-factor
inclusions gives left `R`- and right `S`-actions on its objects. -/
abbrev coefficientCategory := ModuleCat.{v} (R ⊗[ℤ] Sᵐᵒᵖ)

/-- Left R action of a tensor-product-ring coefficient object.

For a coefficient object `X`, restrict its `R ⊗[ℤ] Sᵐᵒᵖ`-module structure along the left ring
inclusion to obtain a left `R`-module structure. -/
def coefficientLeftModule (X : coefficientCategory R S) : Module R X :=
  Module.compHom X
    (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℤ] Sᵐᵒᵖ)

/-- Right S action of a tensor-product-ring coefficient object.

For a coefficient object `X`, restrict scalars along the right inclusion of `Sᵐᵒᵖ` in `R ⊗[ℤ]
Sᵐᵒᵖ` to obtain its right `S`-module structure. -/
def coefficientRightModule (X : coefficientCategory R S) : Module Sᵐᵒᵖ X :=
  Module.compHom X
    (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[ℤ] R ⊗[ℤ] Sᵐᵒᵖ).toRingHom

/-- Tensor-product coefficient actions commute.

The restricted left `R`-action and right `S`-action on a coefficient object commute, since the
images of the two tensor-factor inclusions commute. -/
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

/-- Additive tensor functor of a tensor-product-ring coefficient.

A coefficient object `X`, with its two restricted actions, defines the additive functor `A ↦ A
⊗_R X` from right `R`-modules to right `S`-modules. -/
def coefficientTensorObj (X : coefficientCategory R S) :
    ModuleCat.{v} Rᵐᵒᵖ ⥤+ ModuleCat.{v} Sᵐᵒᵖ := by
  letI := coefficientLeftModule R S X
  letI := coefficientRightModule R S X
  letI := coefficientActionsCommute R S X
  exact AdditiveFunctor.of (tensorFunctor R S X)

/-- Left-linear restriction of a coefficient-category morphism.

A morphism `f : X ⟶ Y` over `R ⊗[ℤ] Sᵐᵒᵖ` gives an `R`-linear map between the restricted left-
module structures on `X` and `Y`. -/
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

/-- Restricted coefficient morphism preserves the right S action.

For a coefficient-category morphism `f`, its restricted left-linear map satisfies `f (s • x) =
s • f x` for every `s : Sᵐᵒᵖ`. -/
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

/-- Coefficient-category morphism gives a tensor natural transformation.

A morphism of tensor-product-ring coefficient modules induces a natural transformation between
their additive right-module tensor functors. -/
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

/-- Coefficient modules as a functor to additive tensor functors.

The assignment from coefficient objects to their additive tensor functors, and from
coefficient morphisms to their tensor natural transformations, defines a functor. -/
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

/-- The coefficient-to-tensor-functor assignment is additive.

The functor from `ModuleCat (R ⊗[ℤ] Sᵐᵒᵖ)` to additive right-module tensor functors preserves
sums of coefficient morphisms. -/
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

/-- Bundled additive assignment of coefficient tensor functors.

Bundle the coefficient-to-tensor-functor assignment with its additivity as an additive functor
into the category of additive functors from right `R`-modules to right `S`-modules. -/
def coefficientTensorAdditiveFunctor :
    coefficientCategory R S ⥤+
      (ModuleCat.{v} Rᵐᵒᵖ ⥤+ ModuleCat.{v} Sᵐᵒᵖ) := by
  letI := coefficientTensorFunctor_additive R S
  exact AdditiveFunctor.of (coefficientTensorFunctor R S)

/-- Coefficient category maps to Tor functors in each degree.

Assuming right `R`-modules have projective resolutions, compose the coefficient tensor-functor
assignment with degree-`n` left derivation to obtain a functor from coefficient modules to
right-module-valued Tor functors. -/
def coefficientTorFunctor [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)] (n : ℕ) :
    coefficientCategory R S ⥤ (ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} Sᵐᵒᵖ) :=
  coefficientTensorFunctor R S ⋙
    CategoryTheory.leftDerivedDegreeFunctor
      (ModuleCat.{v} Rᵐᵒᵖ) (ModuleCat.{v} Sᵐᵒᵖ) n

end NativeCoefficientCategory

section OriginalActions

open scoped TensorProduct

/-- Commuting bimodule actions define a coefficient-category object.

A coefficient `B` with commuting left `R`- and right `S`-actions has an induced module
structure over `R ⊗[ℤ] Sᵐᵒᵖ`, giving an object of the coefficient category on the carrier `B`. -/
def coefficientObjectOfActions : coefficientCategory R S := by
  letI : Module (R ⊗[ℤ] Sᵐᵒᵖ) B := TensorProduct.Algebra.module
  exact ModuleCat.of (R ⊗[ℤ] Sᵐᵒᵖ) B

/-- Constructed coefficient object retains its given left action.

Restricting the tensor-product-ring coefficient object of `B` along the left inclusion gives
the same scalar values `r • x` as the given left `R`-action. -/
theorem coefficientObjectOfActions_left (r : R) (x : B) :
    (coefficientLeftModule R S (coefficientObjectOfActions R S B)).smul r x =
      r • x := by
  change r • ((1 : Sᵐᵒᵖ) • x) = r • x
  rw [one_smul]

/-- Constructed coefficient object retains its given right action.

Restricting the coefficient object of `B` along the right inclusion gives the same scalar
values `s • x` as the given right `S`-action. -/
theorem coefficientObjectOfActions_right (s : Sᵐᵒᵖ) (x : B) :
    (coefficientRightModule R S (coefficientObjectOfActions R S B)).smul s x =
      s • x := by
  change (1 : R) • (s • x) = s • x
  rw [one_smul]

/-- Map preserving bimodule actions gives a coefficient-category morphism.

An `R`-linear map `f : B → B'` preserving the right `S`-action is linear over the induced
tensor-product-ring module structures, and hence defines a coefficient-category morphism. -/
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

/-- Constructed coefficient-category morphism retains its function values.

The coefficient-category morphism induced by a compatible bimodule map `f` evaluates at `x :
B` as `f x`. -/
theorem coefficientMapOfActions_apply (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (x : B) :
    (coefficientMapOfActions R S B B' f hf).hom x = f x := rfl

end OriginalActions

end ModuleCat.BalancedTensorRight
