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
# Actual coefficient precomposition on enriched Hom and Ext

A morphism of the original R-left/S-right coefficients gives precomposition
on S-linear Hom, retaining the existing right R-action. Its native right
derivation gives the coefficient transformation on the existing Ext functors.
The target coefficient module has no supplied R-action, and no comparison,
projectivity or functor-law conclusion is supplied as input.
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
  (f : B →ₗ[Sᵐᵒᵖ] B')
  (hR : ∀ (r : R) (b : B), f (r • b) = r • f b)

/-- The actual coefficient precomposition on the original Hom objects. -/
def homCoefficientMap (C : ModuleCat.{v} Sᵐᵒᵖ) :
    homObj R S B' C ⟶ homObj R S B C := by
  dsimp only [homObj]
  letI := TensorProduct.Balanced.CoefficientHom.homModule R S B C
  letI := TensorProduct.Balanced.CoefficientHom.homModule R S B' C
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.precomp
      (R := R) (S := S) (B := B) (B' := B') (C := C) f hR)

/-- Precomposition keeps its original value on each coefficient element. -/
@[simp]
theorem homCoefficientMap_apply (C : ModuleCat.{v} Sᵐᵒᵖ)
    (g : TensorProduct.Balanced.CoefficientHom.Hom S B' C) (b : B) :
    (homCoefficientMap R S B B' f hR C).hom g b = g (f b) := rfl

/-- The coefficient map is natural in the actual S-module target, without an R-action there. -/
theorem homCoefficientMap_naturality {C C' : ModuleCat.{v} Sᵐᵒᵖ} (g : C ⟶ C') :
    homMap R S B' g ≫ homCoefficientMap R S B B' f hR C' =
      homCoefficientMap R S B B' f hR C ≫ homMap R S B g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  dsimp only [homObj] at h
  apply LinearMap.ext
  intro b
  rfl

set_option linter.unusedVariables false in
/-- The actual Hom functors are contravariant in the original coefficient. -/
def homCoefficientTransformation : homFunctor R S B' ⟶ homFunctor R S B where
  app := homCoefficientMap R S B B' f hR
  naturality {C C'} g := homCoefficientMap_naturality R S B B' f hR g

/-- The transformation uses the already constructed native Hom components. -/
theorem homCoefficientTransformation_app (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (homCoefficientTransformation R S B B' f hR).app C =
      homCoefficientMap R S B B' f hR C := rfl

/-- The identity coefficient map induces the actual identity Hom transformation. -/
theorem homCoefficientTransformation_id :
    homCoefficientTransformation R S B B (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B)
      (fun _ _ => rfl) = 𝟙 (homFunctor R S B) := by
  apply NatTrans.ext
  funext C
  apply ModuleCat.hom_ext
  let := TensorProduct.Balanced.CoefficientHom.homModule R S B C
  change TensorProduct.Balanced.CoefficientHom.precomp
      (R := R) (S := S) (B := B) (B' := B) (C := C)
      (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B) (fun _ _ => rfl) = LinearMap.id
  exact TensorProduct.Balanced.CoefficientHom.precomp_id
    (R := R) (S := S) (B := B) (C := C)

variable (B'' : Type v) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'']
  (g : B' →ₗ[Sᵐᵒᵖ] B'')
  (hRg : ∀ (r : R) (b : B'), g (r • b) = r • g b)

/-- Coefficient composition is reversed by actual Hom precomposition. -/
theorem homCoefficientTransformation_comp :
    homCoefficientTransformation R S B' B'' g hRg ≫
        homCoefficientTransformation R S B B' f hR =
      homCoefficientTransformation R S B B'' (g.comp f)
        (fun r b => (congrArg g (hR r b)).trans (hRg r (f b))) := by
  apply NatTrans.ext
  funext C
  apply ModuleCat.hom_ext
  let := TensorProduct.Balanced.CoefficientHom.homModule R S B C
  let := TensorProduct.Balanced.CoefficientHom.homModule R S B' C
  let := TensorProduct.Balanced.CoefficientHom.homModule R S B'' C
  change (TensorProduct.Balanced.CoefficientHom.precomp
      (R := R) (S := S) (B := B) (B' := B') (C := C) f hR).comp
      (TensorProduct.Balanced.CoefficientHom.precomp
        (R := R) (S := S) (B := B') (B' := B'') (C := C) g hRg) =
    TensorProduct.Balanced.CoefficientHom.precomp
      (R := R) (S := S) (B := B) (B' := B'') (C := C) (g.comp f)
      (fun r b => (congrArg g (hR r b)).trans (hRg r (f b)))
  exact (TensorProduct.Balanced.CoefficientHom.precomp_comp
    (R := R) (S := S) (B := B) (B' := B') (B'' := B'') (C := C)
    f g hR hRg).symm

section Ext

variable [HasInjectiveResolutions (ModuleCat.{v} Sᵐᵒᵖ)]

/-- Native right derivation of actual coefficient precomposition. -/
def extCoefficientTransformation (n : ℕ) :
    extFunctor R S B' n ⟶ extFunctor R S B n :=
  NatTrans.rightDerived (homCoefficientTransformation R S B B' f hR) n

/-- The actual enriched Ext map, contravariant in B and covariant in C. -/
def extCoefficientMap (n : ℕ) (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (extFunctor R S B' n).obj C ⟶ (extFunctor R S B n).obj C :=
  (extCoefficientTransformation R S B B' f hR n).app C

/-- Target-variable naturality is the native derived-transformation square. -/
theorem extCoefficientMap_naturality (n : ℕ)
    {C C' : ModuleCat.{v} Sᵐᵒᵖ} (c : C ⟶ C') :
    (extFunctor R S B' n).map c ≫ extCoefficientMap R S B B' f hR n C' =
      extCoefficientMap R S B B' f hR n C ≫ (extFunctor R S B n).map c :=
  (extCoefficientTransformation R S B B' f hR n).naturality c

/-- Identity coefficients induce the identity on the existing native Ext functor. -/
theorem extCoefficientTransformation_id (n : ℕ) :
    extCoefficientTransformation R S B B (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B)
      (fun _ _ => rfl) n = 𝟙 (extFunctor R S B n) := by
  rw [extCoefficientTransformation, homCoefficientTransformation_id, NatTrans.rightDerived_id]
  rfl

/-- The native derived composition law retains contravariance in the coefficient. -/
theorem extCoefficientTransformation_comp (n : ℕ) :
    extCoefficientTransformation R S B' B'' g hRg n ≫
        extCoefficientTransformation R S B B' f hR n =
      extCoefficientTransformation R S B B'' (g.comp f)
        (fun r b => (congrArg g (hR r b)).trans (hRg r (f b))) n := by
  change NatTrans.rightDerived (homCoefficientTransformation R S B' B'' g hRg) n ≫
      NatTrans.rightDerived (homCoefficientTransformation R S B B' f hR) n =
    NatTrans.rightDerived (homCoefficientTransformation R S B B'' (g.comp f)
      (fun r b => (congrArg g (hR r b)).trans (hRg r (f b)))) n
  rw [← NatTrans.rightDerived_comp, homCoefficientTransformation_comp]

/-- An actual injective resolution computes the coefficient Ext map by precomposition. -/
theorem extCoefficientTransformation_resolution (n : ℕ)
    {C : ModuleCat.{v} Sᵐᵒᵖ} (I : InjectiveResolution C) :
    (extCoefficientTransformation R S B B' f hR n).app C =
      (I.isoRightDerivedObj (homFunctor R S B') n).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} Rᵐᵒᵖ)
          (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (homCoefficientTransformation R S B B' f hR) (ComplexShape.up ℕ)).app I.cocomplex) ≫
        (I.isoRightDerivedObj (homFunctor R S B) n).inv :=
  InjectiveResolution.rightDerived_app_eq
    (homCoefficientTransformation R S B B' f hR) I n

end Ext

end ModuleCat.BalancedTensorRight
