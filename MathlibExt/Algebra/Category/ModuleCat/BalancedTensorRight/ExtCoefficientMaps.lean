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
# Contravariant bimodule coefficient maps on Hom and Ext

Let `B` and `B'` be `R`-left, `S`-right bimodules. An `Sᵐᵒᵖ`-linear map `f : B → B'`
preserving the left `R`-action induces precomposition `Hom_(Sᵐᵒᵖ)(B', C) → Hom_(Sᵐᵒᵖ)(B, C)`,
linear for the right `R`-action and natural in the right `S`-module `C`.

When right `S`-modules have injective resolutions, right derivation gives `Ext^n_(Sᵐᵒᵖ)(B', C)
→ Ext^n_(Sᵐᵒᵖ)(B, C)` in every degree. Identities and coefficient composition obey this
contravariant order. On an injective resolution of `C`, the map is the cochain homology map of
degreewise precomposition. The target `C` carries the required right `S`-action.
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

/-- Right-linear coefficient precomposition on Hom.

An `Sᵐᵒᵖ`-linear coefficient map `f : B → B'` preserving the left `R`-action induces a right
`R`-linear map `homObj R S B' C ⟶ homObj R S B C` by precomposition. -/
def homCoefficientMap (C : ModuleCat.{v} Sᵐᵒᵖ) :
    homObj R S B' C ⟶ homObj R S B C := by
  dsimp only [homObj]
  letI := TensorProduct.Balanced.CoefficientHom.homModule R S B C
  letI := TensorProduct.Balanced.CoefficientHom.homModule R S B' C
  exact ModuleCat.ofHom
    (TensorProduct.Balanced.CoefficientHom.precomp
      (R := R) (S := S) (B := B) (B' := B') (C := C) f hR)

/-- Coefficient Hom precomposition on elements.

For an `Sᵐᵒᵖ`-linear map `g : B' → C` and `b : B`, the coefficient Hom map evaluates as `g(f
b)`. -/
@[simp]
theorem homCoefficientMap_apply (C : ModuleCat.{v} Sᵐᵒᵖ)
    (g : TensorProduct.Balanced.CoefficientHom.Hom S B' C) (b : B) :
    (homCoefficientMap R S B B' f hR C).hom g b = g (f b) := rfl

/-- Coefficient Hom precomposition is natural in the target module.

Postcomposition with a right `S`-module map `g : C ⟶ C'` commutes with coefficient
precomposition by `f`. -/
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
/-- Coefficient precomposition as a Hom natural transformation.

The maps induced by `f : B → B'` form a natural transformation `homFunctor R S B' ⟶ homFunctor
R S B`, reversing the coefficient direction. -/
def homCoefficientTransformation : homFunctor R S B' ⟶ homFunctor R S B where
  app := homCoefficientMap R S B B' f hR
  naturality {C C'} g := homCoefficientMap_naturality R S B B' f hR g

/-- Component of the coefficient Hom precomposition transformation.

At a right `S`-module `C`, the coefficient Hom natural transformation has component
`homCoefficientMap R S B B' f hR C`. -/
theorem homCoefficientTransformation_app (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (homCoefficientTransformation R S B B' f hR).app C =
      homCoefficientMap R S B B' f hR C := rfl

/-- Identity coefficient gives the identity Hom transformation.

The precomposition natural transformation induced by the identity coefficient map is the
identity of `homFunctor R S B`. -/
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

/-- Hom coefficient transformations compose contravariantly.

For `f : B → B'` and `g : B' → B''` preserving both actions, precomposition by `g`, followed
by precomposition by `f`, equals precomposition by `g.comp f`. -/
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

/-- Coefficient precomposition right derives to an Ext transformation.

Assuming injective resolutions for right `S`-modules, right derive the coefficient Hom
transformation to obtain `extFunctor R S B' n ⟶ extFunctor R S B n`. -/
def extCoefficientTransformation (n : ℕ) :
    extFunctor R S B' n ⟶ extFunctor R S B n :=
  NatTrans.rightDerived (homCoefficientTransformation R S B B' f hR) n

/-- Contravariant coefficient map on a right-module Ext object.

At a right `S`-module `C`, the degree-`n` derived precomposition transformation gives a right
`R`-linear map from the Ext object with coefficient `B'` to that with coefficient `B`. -/
def extCoefficientMap (n : ℕ) (C : ModuleCat.{v} Sᵐᵒᵖ) :
    (extFunctor R S B' n).obj C ⟶ (extFunctor R S B n).obj C :=
  (extCoefficientTransformation R S B B' f hR n).app C

/-- Contravariant coefficient Ext map is natural in the target.

For a right `S`-module morphism `c : C ⟶ C'`, the induced Ext maps commute with the
coefficient precomposition maps in degree `n`. -/
theorem extCoefficientMap_naturality (n : ℕ)
    {C C' : ModuleCat.{v} Sᵐᵒᵖ} (c : C ⟶ C') :
    (extFunctor R S B' n).map c ≫ extCoefficientMap R S B B' f hR n C' =
      extCoefficientMap R S B B' f hR n C ≫ (extFunctor R S B n).map c :=
  (extCoefficientTransformation R S B B' f hR n).naturality c

/-- Identity coefficient gives the identity Ext transformation.

The degree-`n` Ext coefficient transformation induced by the identity map on `B` is the
identity of `extFunctor R S B n`. -/
theorem extCoefficientTransformation_id (n : ℕ) :
    extCoefficientTransformation R S B B (LinearMap.id : B →ₗ[Sᵐᵒᵖ] B)
      (fun _ _ => rfl) n = 𝟙 (extFunctor R S B n) := by
  rw [extCoefficientTransformation, homCoefficientTransformation_id, NatTrans.rightDerived_id]
  rfl

/-- Ext coefficient transformations compose contravariantly.

For compatible coefficient maps `f : B → B'` and `g : B' → B''`, the degree-`n` Ext
transformation of `g`, followed by that of `f`, equals the transformation of `g.comp f`. -/
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

/-- Coefficient Ext map computed on an injective resolution.

For an injective resolution `I` of `C`, the degree-`n` coefficient Ext map is the source
resolution coordinate, followed by the cochain homology map of the Hom coefficient
transformation on `I.cocomplex`, followed by the inverse target resolution coordinate. -/
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
