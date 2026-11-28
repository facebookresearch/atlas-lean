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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Derived

/-!
# Bimodule coefficient maps on right-module-valued tensor and Tor

Let `B` and `B'` be `R`-left, `S`-right bimodules and `f : B →ₗ[R] B'` a map preserving the
right `S`-action. It induces right `S`-linear maps `A ⊗_R B → A ⊗_R B'`, natural in the right
`R`-module `A`, with `[a ⊗ b] ↦ [a ⊗ f b]`.

When right `R`-modules have projective resolutions, the coefficient transformation left
derives to maps on Tor in all degrees. These transformations preserve identities and
composition. On a projective resolution, the derived map is the homology map of the degreewise
coefficient transformation between the two tensor complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced

universe r s v

namespace ModuleCat.BalancedTensorRight

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B B' : Type v) [AddCommGroup B] [AddCommGroup B']
  [Module R B] [Module R B'] [Module Sᵐᵒᵖ B] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B')
  (hS : ∀ (s : Sᵐᵒᵖ) (b : B), f (s • b) = s • f b)

/-- Right-linear tensor map from a bimodule coefficient morphism.

An `R`-linear coefficient map `f : B → B'` preserving the right `S`-action induces `A ⊗_R B ⟶
A ⊗_R B'` in the right `S`-module category. -/
def tensorCoefficientMap (A : ModuleCat.{v} Rᵐᵒᵖ) :
    tensorObj R S B A ⟶ tensorObj R S B' A := by
  letI := rightModule ℤ R S A B
  letI := rightModule ℤ R S A B'
  let fS : B →ₗ[Sᵐᵒᵖ] B' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' s b := by
        simpa only [RingHom.id_apply] using hS s b }
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.coefficientTensorMap
      (R := R) (S := S) (B := B) (B' := B') (A := A) fS
      (fun r b => f.map_smul r b))

/-- Bimodule coefficient tensor map on pure classes.

The map induced by the coefficient morphism `f` sends `[a ⊗ b]` to `[a ⊗ f b]`. -/
theorem tensorCoefficientMap_mk (A : ModuleCat.{v} Rᵐᵒᵖ) (a : A) (b : B) :
    (tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b) =
      mk ℤ R A B' a (f b) := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B'
  let fS : B →ₗ[Sᵐᵒᵖ] B' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' s b := by
        simpa only [RingHom.id_apply] using hS s b }
  change TensorProduct.Balanced.CoefficientHom.coefficientTensorMap
      (R := R) (S := S) (B := B) (B' := B') (A := A) fS
      (fun r b => f.map_smul r b) (mk ℤ R A B a b) = mk ℤ R A B' a (f b)
  exact TensorProduct.Balanced.CoefficientHom.coefficientTensorMap_mk
    (R := R) (S := S) (B := B) (B' := B') (A := A) fS
    (fun r b => f.map_smul r b) a b

/-- Bimodule coefficient tensor map is natural in the right module.

A right-module map on the first tensor factor commutes with the coefficient map on the second
factor, giving the naturality square for `A ⊗_R f`. -/
theorem tensorCoefficientMap_naturality {A A' : ModuleCat.{v} Rᵐᵒᵖ} (g : A ⟶ A') :
    tensorMap R S B g ≫ tensorCoefficientMap R S B B' f hS A' =
      tensorCoefficientMap R S B B' f hS A ≫ tensorMap R S B' g := by
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A' B'
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B B' f hS A').hom
      ((tensorMap R S B g).hom (mk ℤ R A B a b)) =
    (tensorMap R S B' g).hom
      ((tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b))
  rw [tensorMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorMap_mk]

set_option linter.unusedVariables false in
/-- Bimodule coefficient map as a right-module tensor natural transformation.

The maps `A ⊗_R f` form a natural transformation `tensorFunctor R S B ⟶ tensorFunctor R S B'`. -/
def tensorCoefficientTransformation : tensorFunctor R S B ⟶ tensorFunctor R S B' where
  app := tensorCoefficientMap R S B B' f hS
  naturality {A A'} g := tensorCoefficientMap_naturality R S B B' f hS g

/-- Component of the right-module tensor coefficient transformation.

At a right module `A`, the coefficient natural transformation has component
`tensorCoefficientMap R S B B' f hS A`. -/
theorem tensorCoefficientTransformation_app (A : ModuleCat.{v} Rᵐᵒᵖ) :
    (tensorCoefficientTransformation R S B B' f hS).app A =
      tensorCoefficientMap R S B B' f hS A := rfl

/-- Identity bimodule coefficient gives the identity tensor transformation.

The coefficient transformation induced by the identity map on `B` is the identity of
`tensorFunctor R S B`. -/
theorem tensorCoefficientTransformation_id :
    tensorCoefficientTransformation R S B B (LinearMap.id : B →ₗ[R] B)
      (fun _ _ => rfl) = 𝟙 (tensorFunctor R S B) := by
  apply NatTrans.ext
  funext A
  let := rightModule ℤ R S A B
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B B LinearMap.id (fun _ _ => rfl) A).hom
      (mk ℤ R A B a b) = mk ℤ R A B a b
  rw [tensorCoefficientMap_mk, LinearMap.id_apply]

variable (B'' : Type v) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'']
  (g : B' →ₗ[R] B'')
  (hSg : ∀ (s : Sᵐᵒᵖ) (b : B'), g (s • b) = s • g b)

/-- Right-module tensor coefficient transformations preserve composition.

The tensor coefficient transformation of `f : B → B'`, followed by that of `g : B' → B''`,
equals the transformation of `g.comp f`. -/
theorem tensorCoefficientTransformation_comp :
    tensorCoefficientTransformation R S B B' f hS ≫
        tensorCoefficientTransformation R S B' B'' g hSg =
      tensorCoefficientTransformation R S B B'' (g.comp f)
        (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) := by
  apply NatTrans.ext
  funext A
  let := rightModule ℤ R S A B
  let := rightModule ℤ R S A B''
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R A B
  intro a b
  change (tensorCoefficientMap R S B' B'' g hSg A).hom
      ((tensorCoefficientMap R S B B' f hS A).hom (mk ℤ R A B a b)) =
    (tensorCoefficientMap R S B B'' (g.comp f)
      (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) A).hom (mk ℤ R A B a b)
  rw [tensorCoefficientMap_mk, tensorCoefficientMap_mk, tensorCoefficientMap_mk]
  rfl

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Bimodule coefficient transformation derived on Tor.

Assuming projective resolutions for right `R`-modules, the degree-`n` left-derived tensor
coefficient transformation gives `torFunctor R S B n ⟶ torFunctor R S B' n`. -/
def torCoefficientTransformation (n : ℕ) :
    torFunctor R S B n ⟶ torFunctor R S B' n :=
  NatTrans.leftDerived (tensorCoefficientTransformation R S B B' f hS) n

/-- Bimodule coefficient map on a Tor object.

At a right module `A`, evaluate the degree-`n` derived coefficient transformation to obtain
the right `S`-linear map between the two Tor objects. -/
def torCoefficientMap (n : ℕ) (A : ModuleCat.{v} Rᵐᵒᵖ) :
    (torFunctor R S B n).obj A ⟶ (torFunctor R S B' n).obj A :=
  (torCoefficientTransformation R S B B' f hS n).app A

/-- Derived coefficient Tor map is natural in the right module.

For a right-module morphism `a : A ⟶ A'`, its Tor maps commute with the coefficient maps from
`B` to `B'` in degree `n`. -/
theorem torCoefficientMap_naturality (n : ℕ)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (a : A ⟶ A') :
    (torFunctor R S B n).map a ≫ torCoefficientMap R S B B' f hS n A' =
      torCoefficientMap R S B B' f hS n A ≫ (torFunctor R S B' n).map a :=
  (torCoefficientTransformation R S B B' f hS n).naturality a

/-- Identity bimodule coefficient gives the identity Tor transformation.

The degree-`n` Tor coefficient transformation induced by the identity map on `B` is the
identity of `torFunctor R S B n`. -/
theorem torCoefficientTransformation_id (n : ℕ) :
    torCoefficientTransformation R S B B (LinearMap.id : B →ₗ[R] B)
      (fun _ _ => rfl) n = 𝟙 (torFunctor R S B n) := by
  rw [torCoefficientTransformation, tensorCoefficientTransformation_id,
    NatTrans.leftDerived_id]
  rfl

/-- Derived coefficient Tor transformations preserve composition.

The degree-`n` Tor transformations of `f` and `g` compose to the transformation of `g.comp f`. -/
theorem torCoefficientTransformation_comp (n : ℕ) :
    torCoefficientTransformation R S B B' f hS n ≫
        torCoefficientTransformation R S B' B'' g hSg n =
      torCoefficientTransformation R S B B'' (g.comp f)
        (fun s b => (congrArg g (hS s b)).trans (hSg s (f b))) n := by
  change NatTrans.leftDerived (tensorCoefficientTransformation R S B B' f hS) n ≫
      NatTrans.leftDerived (tensorCoefficientTransformation R S B' B'' g hSg) n =
    NatTrans.leftDerived (tensorCoefficientTransformation R S B B'' (g.comp f)
      (fun s b => (congrArg g (hS s b)).trans (hSg s (f b)))) n
  rw [← NatTrans.leftDerived_comp, tensorCoefficientTransformation_comp]

/-- Coefficient Tor transformation computed on a projective resolution.

For a projective resolution `P` of `A`, the degree-`n` coefficient Tor map is the source
resolution-to-derived coordinate, followed by the homology map of the coefficient
transformation applied to `P.complex`, followed by the inverse target resolution coordinate. -/
theorem torCoefficientTransformation_resolution (n : ℕ)
    {A : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveResolution A) :
    (torCoefficientTransformation R S B B' f hS n).app A =
      (P.isoLeftDerivedObj (tensorFunctor R S B) n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} Sᵐᵒᵖ)
          (ComplexShape.down ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (tensorCoefficientTransformation R S B B' f hS) (ComplexShape.down ℕ)).app P.complex) ≫
        (P.isoLeftDerivedObj (tensorFunctor R S B') n).inv :=
  ProjectiveResolution.leftDerived_app_eq
    (tensorCoefficientTransformation R S B B' f hS) P n

end Tor

end ModuleCat.BalancedTensorRight
