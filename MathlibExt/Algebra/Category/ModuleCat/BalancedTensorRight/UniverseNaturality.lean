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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Universe
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientMapsAdditive
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientIsomorphisms
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPostcomposition
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality
public import MathlibExt.CategoryTheory.Functor.ComparisonTransport
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.TransportComparison

/-!
# Enlarged-source Tor with independent input carriers

Left derivation takes place in Gamma, followed by precomposition with the
input category, which need not have enough projectives. Coefficient and
height comparisons use mapped resolutions and exact postcomposition.
Zero-augmentation squares and identity, inverse and composition triangles
are expressed after a common third working lift, with distinct input
categories retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped TensorProduct
universe zGlobal tGlobal rGlobal sGlobal aGlobal bGlobal
namespace ModuleCat.BalancedTensorRight
variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type bGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

instance largeTensorFunctorAt_additive.{z, r, s, a, b} (R : Type r) (S : Type s)
    [Ring R] [Ring S] (B : Type b) [AddCommGroup B] [Module R B]
    [Module Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B] :
    (largeTensorFunctorAt.{z, r, s, a, b} R S B).Additive :=
  tensorFunctor_additive R S (ULift.{max r a b z} B)

/-- The actual native Tor functor is derived in the sufficient carrier universe. -/
def torFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ ⋙
    torFunctor R S (ULift.{max r a b z} B) n

/-- The original right module supplies an actual lifted input to native Tor. -/
abbrev torObjAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  (torFunctorAt.{z, r, s, a, b} R S B n).obj X

/-- Original input maps use the native derived functor after native input lifting. -/
def torMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) {X Y : ModuleCat.{a} Rᵐᵒᵖ} (f : X ⟶ Y) :
    torObjAt.{z, r, s, a, b} R S B n X ⟶ torObjAt.{z, r, s, a, b} R S B n Y :=
  (torFunctorAt.{z, r, s, a, b} R S B n).map f

/-- Native right exactness identifies degree zero with the actual lifted balanced tensor. -/
def torZeroIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    torFunctorAt.{z, r, s, a, b} R S B 0 ≅
      tensorFunctorAt.{z, r, s, a, b} R S B := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (torZeroIso R S (ULift.{max r a b z} B))

/-- The zero map is the original native augmentation map at the actual lifted input. -/
theorem torZeroIsoAt_hom_app.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
    (torZeroIsoAt.{z, r, s, a, b} R S B).hom.app X =
      (tensorFunctor R S (ULift.{max r a b z} B)).fromLeftDerivedZero.app
        ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) := rfl

/-- Any actual resolution of the lifted original input computes this same native Tor. -/
def torResolutionIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ)
    (P : ProjectiveResolution
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) :
    torObjAt.{z, r, s, a, b} R S B n X ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{max r a b z} Sᵐᵒᵖ)
        (ComplexShape.down ℕ) n).obj
        (((largeTensorFunctorAt.{z, r, s, a, b} R S B).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj (tensorFunctor R S (ULift.{max r a b z} B)) n

section Coefficients

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- The original coefficient map is lifted by native up-f-down, retaining R-linearity. -/
def liftedCoefficientMapAt.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (f : B →ₗ[R] B') :
    ULift.{max r a b z} B →ₗ[R] ULift.{max r a b z} B' :=
  (ULift.moduleEquiv : ULift.{max r a b z} B' ≃ₗ[R] B').symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{max r a b z} B ≃ₗ[R] B).toLinearMap)

/-- The actual lifted coefficient map keeps the given right S-action. -/
theorem liftedCoefficientMapAt_outer.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (s : Sᵐᵒᵖ) (x : ULift.{max r a b z} B) :
    liftedCoefficientMapAt.{z, r, a, b} R B B' f (s • x) =
      s • liftedCoefficientMapAt.{z, r, a, b} R B B' f x :=
  congrArg ULift.up (hf s x.down)

/-- The actual coefficient transformation before restricting the original input category. -/
def largeTensorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    largeTensorFunctorAt.{z, r, s, a, b} R S B ⟶
      largeTensorFunctorAt.{z, r, s, a, b} R S B' :=
  tensorCoefficientTransformation R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)

/-- Derive the same actual coefficient transformation in the sufficient source category. -/
def largeTorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    torFunctor R S (ULift.{max r a b z} B) n ⟶
      torFunctor R S (ULift.{max r a b z} B') n :=
  NatTrans.leftDerived (largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf) n

/-- Coefficient morphisms act on the working tensor functor. -/
def tensorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    tensorFunctorAt.{z, r, s, a, b} R S B ⟶
      tensorFunctorAt.{z, r, s, a, b} R S B' :=
  Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (tensorCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))

/-- The coefficient transformation changes the original coefficient on each pure tensor. -/
theorem tensorCoefficientTransformationAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B') (ULift.up x) (ULift.up (f y)) := by
  change (tensorCoefficientMap R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)).hom _ = _
  exact tensorCoefficientMap_mk R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)
    (ULift.up x) (ULift.up y)

/-- The coefficient Tor map is derived only in the sufficient source universe. -/
def torCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⟶
      torFunctorAt.{z, r, s, a, b} R S B' n :=
  Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (torCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n)

/-- Native resolution computation retains the actual original coefficient morphism. -/
theorem torCoefficientTransformationAt_resolution.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ)
    (P : ProjectiveResolution
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) :
    (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n).app X =
      (torResolutionIsoAt R S B n X P).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{max r a b z} Sᵐᵒᵖ)
          (ComplexShape.down ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (tensorCoefficientTransformation R S
              (ULift.{max r a b z} B) (ULift.{max r a b z} B')
              (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
              (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))
            (ComplexShape.down ℕ)).app P.complex) ≫
          (torResolutionIsoAt R S B' n X P).inv :=
  torCoefficientTransformation_resolution R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n P

/-- Degree-zero identification is natural in every original coefficient map. -/
theorem torZeroIsoAt_naturality_coefficient.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf 0 ≫
        (torZeroIsoAt R S B').hom =
      (torZeroIsoAt R S B).hom ≫
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf := by
  have h := NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor
    (tensorCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))
  exact congrArg (Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)) h

/-- Original lifted coefficient maps preserve zero without requiring commutative scalars. -/
theorem liftedCoefficientMapAt_zero.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] :
    liftedCoefficientMapAt.{z, r, a, b} R B B' (0 : B →ₗ[R] B') = 0 := by
  apply LinearMap.ext
  intro x
  rfl

/-- The up-f-down construction is additive on the original coefficient maps. -/
theorem liftedCoefficientMapAt_add.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (f : B →ₗ[R] B') (g : B →ₗ[R] B') :
    liftedCoefficientMapAt.{z, r, a, b} R B B' (f + g) =
      liftedCoefficientMapAt.{z, r, a, b} R B B' f + liftedCoefficientMapAt.{z, r, a, b} R B B' g := by
  apply LinearMap.ext
  intro x
  rfl

/-- The working tensor transformation is zero on the zero original coefficient morphism. -/
theorem tensorCoefficientTransformationAt_zero.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' 0
      (by intro s x; simp only [LinearMap.zero_apply, smul_zero]) = 0 := by
  unfold tensorCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_zero, tensorCoefficientTransformation_zero]
  rfl

/-- Working tensor coefficient maps retain original addition. -/
theorem tensorCoefficientTransformationAt_add.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (g : B →ₗ[R] B')
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B), g (s • x) = s • g x) :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) =
      tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf +
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r a b z} X) (ULift.{max r a b z} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  have hSum := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B'
    (f + g) (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) X x y
  have hF := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B' f hf X x y
  have hG := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B' g hg X x y
  change ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
      (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add])).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) = _
  rw [hSum]
  change TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
      (ULift.{max r a b z} B') (ULift.up x) (ULift.up ((f + g) y)) =
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) +
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y))
  rw [hF, hG, LinearMap.add_apply]
  exact (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
    (ULift.{max r a b z} B') (ULift.up x)).map_add _ _

/-- Native Tor is additive on the zero original coefficient morphism. -/
theorem torCoefficientTransformationAt_zero.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' 0
      (by intro s x; simp only [LinearMap.zero_apply, smul_zero]) n = 0 := by
  unfold torCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_zero, torCoefficientTransformation_zero]
  rfl

/-- Native derived coefficient maps retain original addition and hence integer actions. -/
theorem torCoefficientTransformationAt_add.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (g : B →ₗ[R] B')
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B), g (s • x) = s • g x) (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) n =
      torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n +
        torCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg n := by
  apply NatTrans.ext
  funext X
  have h := torCoefficientTransformation_add R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt.{z, r, a, b} R B B' g)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' g hg) n
  have hX := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) h
  change (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' (f + g))
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add])) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) =
    (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B') (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) +
    (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B') (liftedCoefficientMapAt.{z, r, a, b} R B B' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' g hg) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)
  simpa only [liftedCoefficientMapAt_add, NatTrans.app_add] using hX

/-- Package all legitimate additive scalar laws on actual original coefficient maps. -/
def torCoefficientAddHomAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (n : ℕ) :
    coefficientMapGroup R S B B' →+
      (torFunctorAt.{z, r, s, a, b} R S B n ⟶
        torFunctorAt.{z, r, s, a, b} R S B' n) where
  toFun f := torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f.val f.property n
  map_zero' := torCoefficientTransformationAt_zero R S B B' n
  map_add' f g := torCoefficientTransformationAt_add R S B B'
    f.val f.property g.val g.property n

end Coefficients

section CoefficientIdentityComposition

/-- Native lifting retains the original identity coefficient morphism. -/
theorem liftedCoefficientMapAt_id.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B] :
    liftedCoefficientMapAt.{z, r, a, b} R B B LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rfl

/-- Original identity coefficients give the actual tensor identity at every raw input. -/
theorem tensorCoefficientTransformationAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id
      (fun _ _ => rfl) = 𝟙 (tensorFunctorAt.{z, r, s, a, b} R S B) := by
  unfold tensorCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_id, tensorCoefficientTransformation_id]
  rfl

/-- Original identity coefficients give the same native Tor identity in every degree. -/
theorem torCoefficientTransformationAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id
      (fun _ _ => rfl) n = 𝟙 (torFunctorAt.{z, r, s, a, b} R S B n) := by
  unfold torCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_id, torCoefficientTransformation_id]
  rfl

variable (B' B'' : Type bGlobal) [AddCommGroup B'] [AddCommGroup B'']
  [Module R B'] [Module R B''] [Module Sᵐᵒᵖ B'] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'] [SMulCommClass R Sᵐᵒᵖ B'']
  (f : B →ₗ[R] B') (g : B' →ₗ[R] B'')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)
  (hg : ∀ (sGlobal : Sᵐᵒᵖ) (x : B'), g (sGlobal • x) = sGlobal • g x)

/-- Native up-f-down maps compose on the actual original coefficient carriers. -/
theorem liftedCoefficientMapAt_comp.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (B'' : Type b) [AddCommGroup B''] [Module R B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'') :
    liftedCoefficientMapAt.{z, r, a, b} R B B'' (g.comp f) =
      (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g).comp (liftedCoefficientMapAt.{z, r, a, b} R B B' f) := by
  apply LinearMap.ext
  intro x
  rfl

/-- Original coefficient composition is retained on the actual lifted tensor functor. -/
theorem tensorCoefficientTransformationAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (B'' : Type b) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
    [SMulCommClass R Sᵐᵒᵖ B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B'), g (s • x) = s • g x) :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf ≫
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg =
      tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) := by
  apply NatTrans.ext
  funext X
  have h := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X))
    (tensorCoefficientTransformation_comp R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      (ULift.{max r a b z} B'') (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B' B'' g hg))
  exact h

/-- Original coefficient composition is retained by native Tor in every degree. -/
theorem torCoefficientTransformationAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (B'' : Type b) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
    [SMulCommClass R Sᵐᵒᵖ B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B'), g (s • x) = s • g x) (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n ≫
        torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg n =
      torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) n := by
  apply NatTrans.ext
  funext X
  have h := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X))
    (torCoefficientTransformation_comp R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      (ULift.{max r a b z} B'') (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B' B'' g hg) n)
  exact h

end CoefficientIdentityComposition

section CoefficientHeight

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- The actual underived height square is natural in the original coefficient map. -/
theorem tensorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
        (largeTensorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf) ≫
      (tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom =
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom ≫
      Functor.whiskerRight (largeTensorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r a b z t} X) (ULift.{max r a b z t} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  change ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom.app X).hom
      ((tensorCoefficientMap R S
        (ULift.{max r a b z t} B) (ULift.{max r a b z t} B')
        (liftedCoefficientMapAt.{max z t, r, a, b} R B B' f)
        (liftedCoefficientMapAt_outer.{max z t, r, s, a, b} R S B B' f hf)
        ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y))) =
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
      ((largeTensorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf).app X)).hom
      (((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y)))
  have hHigh := tensorCoefficientMap_mk R S
    (ULift.{max r a b z t} B) (ULift.{max r a b z t} B')
    (liftedCoefficientMapAt.{max z t, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{max z t, r, s, a, b} R S B B' f hf)
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)
    (ULift.up x) (ULift.up y)
  have hHeightB := tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} R S B X x y
  have hHeightB' := tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} R S B' X x (f y)
  have hLow := tensorCoefficientMap_mk R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    X x (ULift.up y)
  have hHigh' := congrArg ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom.app X).hom hHigh
  have hHeight' := congrArg
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
      ((largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X)).hom hHeightB
  exact hHigh'.trans (hHeightB'.trans
    ((congrArg ULift.up hLow).symm.trans hHeight'.symm))

end CoefficientHeight

section ParameterFunctors

/-- The actual coefficient functor keeps the raw coefficient world and the enlarged output. -/
def tensorCoefficientFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] :
    coefficientCategory.{r, s, b} R S ⥤
      (ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ) ⋙
    coefficientTensorFunctor R S ⋙
    AdditiveFunctor.forget (ModuleCat.{max r a b z} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Sᵐᵒᵖ) ⋙
    (Functor.whiskeringLeft (ModuleCat.{a} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Rᵐᵒᵖ) (ModuleCat.{max r a b z} Sᵐᵒᵖ)).obj
        (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)

/-- Derive the actual tensor family in Gamma before restricting its original input. -/
def torCoefficientFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] (n : ℕ) :
    coefficientCategory.{r, s, b} R S ⥤
      (ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ) ⋙
    coefficientTorFunctor.{r, s, max r a b z} R S n ⋙
    (Functor.whiskeringLeft (ModuleCat.{a} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Rᵐᵒᵖ) (ModuleCat.{max r a b z} Sᵐᵒᵖ)).obj
        (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)

/-- Flipping the native parameter functor supplies both-variable tensor naturality. -/
def tensorBifunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] :
    ModuleCat.{a} Rᵐᵒᵖ ⥤
      (coefficientCategory.{r, s, b} R S ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  (tensorCoefficientFunctorAt.{z, r, s, a, b} R S).flip

/-- The genuine derived parameter functor supplies both-variable Tor naturality. -/
def torBifunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] (n : ℕ) :
    ModuleCat.{a} Rᵐᵒᵖ ⥤
      (coefficientCategory.{r, s, b} R S ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  (torCoefficientFunctorAt.{z, r, s, a, b} R S n).flip

end ParameterFunctors

section Heights

/-- The sufficient source lift has projective preservation; the target needs only exactness. -/
def largeTorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctor R S (ULift.{max r a b z} B) n ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ ⋙
        torFunctor R S (ULift.{max r a b z t} B) n := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso U V F G
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B) n


/-- The original input is flattened only after native Tor derivation in sufficient worlds. -/
def torHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      torFunctorAt.{max z t, r, s, a, b} R S B n := Functor.precompositionComparisonIso
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (torFunctor R S (ULift.{max r a b z} B) n)
    (torFunctor R S (ULift.{max r a b z t} B) n)
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n)
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)


/-- The same actual input and coefficient flattening give the underived height comparison. -/
def tensorHeightFacadeIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      tensorFunctorAt.{max z t, r, s, a, b} R S B := Functor.precompositionComparisonIso
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (largeTensorFunctorAt.{z, r, s, a, b} R S B)
    (largeTensorFunctorAt.{max z t, r, s, a, b} R S B)
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).symm
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)


/-- The facade component is the actual sufficient-world comparison followed by input flattening. -/
theorem torHeightIsoAt_hom_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app X =
      (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app
          ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) ≫
        (torFunctor R S (ULift.{max r a b z t} B) n).map
          ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
            Rᵐᵒᵖ).hom.app X) := by
  exact Functor.precompositionComparisonIso_hom_app
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (torFunctor R S (ULift.{max r a b z} B) n)
    (torFunctor R S (ULift.{max r a b z t} B) n)
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n)
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)
    X


/-- The tensor facade uses the same input flattening after the inverse tensor square. -/
theorem tensorHeightFacadeIsoAt_hom_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app X =
      (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app
          ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) ≫
        (largeTensorFunctorAt.{max z t, r, s, a, b} R S B).map
          ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
            Rᵐᵒᵖ).hom.app X) := by
  exact Functor.precompositionComparisonIso_hom_app
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (largeTensorFunctorAt.{z, r, s, a, b} R S B)
    (largeTensorFunctorAt.{max z t, r, s, a, b} R S B)
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).symm
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)
    X


/-- The facade height comparison has the original pure value after native input flattening. -/
theorem tensorHeightFacadeIsoAt_hom_mk.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y))) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
        (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y) := by
  rw [tensorHeightFacadeIsoAt_hom_app]
  change (tensorMap R S (ULift.{max r a b z t} B)
      ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)).hom
      (((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app
        ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)))) = _
  have hInv := tensorHeightIsoAt_inv_mk.{t, z, r, s, a, b} R S B
    ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) (ULift.up x) y
  have hInv' := congrArg
    (tensorMap R S (ULift.{max r a b z t} B)
      ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)).hom hInv
  have hMap := tensorMap_mk R S (ULift.{max r a b z t} B)
    (A := ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ) ⋙
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)
    (A' := (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X)
    ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)
    (ULift.up (ULift.up x)) (ULift.up y)
  exact hInv'.trans hMap

/-- All three comparison legs retain the actual degree-zero augmentation. -/
theorem largeTorHeightIsoAt_hom_augmentation.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
    let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B 0).hom ≫
        Functor.whiskerLeft U G.fromLeftDerivedZero ≫
          (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom =
      Functor.whiskerRight (largeTensorFunctorAt.{z, r, s, a, b} R S B).fromLeftDerivedZero
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  change (Functor.leftDerivedTransportIso U V F G e 0).hom ≫
    Functor.whiskerLeft U G.fromLeftDerivedZero ≫ e.hom = Functor.whiskerRight F.fromLeftDerivedZero V
  rw [← Category.assoc, Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


/-- The original-input universe comparison preserves the actual Tor-to-tensor augmentation. -/
theorem torHeightIsoAt_hom_zero.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B 0).hom ≫
        (torZeroIsoAt.{max z t, r, s, a, b} R S B).hom =
      Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
        (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom := by
  let W := ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ
  let W' := ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let s := ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  have h := Functor.precompositionComparisonIso_naturality
    W W' U V (F.leftDerived 0) (G.leftDerived 0)
    (Functor.leftDerivedTransportIso U V F G e 0) s
    F.fromLeftDerivedZero G.fromLeftDerivedZero e.symm
    (Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero U V F G e).symm
  change (Functor.precompositionComparisonIso W W' U V (F.leftDerived 0)
    (G.leftDerived 0) (Functor.leftDerivedTransportIso U V F G e 0) s).hom ≫
      Functor.whiskerLeft W' G.fromLeftDerivedZero =
    Functor.whiskerRight (Functor.whiskerLeft W F.fromLeftDerivedZero) V ≫
      (Functor.precompositionComparisonIso W W' U V F G e.symm s).hom
  exact h.symm


/-- Every original coefficient morphism commutes with all three derived height legs. -/
theorem largeTorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    Functor.whiskerRight (largeTorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf n)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
      (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom =
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom ≫
      Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
        (largeTorCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf n) := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let F' := largeTensorFunctorAt.{z, r, s, a, b} R S B'
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let G' := largeTensorFunctorAt.{max z t, r, s, a, b} R S B'
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  let α := largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf
  let β := largeTensorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let e' := tensorHeightIsoAt.{t, z, r, s, a, b} R S B'
  exact Functor.leftDerivedTransportIso_naturality U V F G e α β e'
    (tensorHeightIsoAt_natural_coefficient R S B B' f hf) n


/-- Actual original coefficient maps commute with the whole-input Tor height comparison. -/
theorem torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    Functor.whiskerRight (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
      (torHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom =
    (torHeightIsoAt.{t, z, r, s, a, b} R S B n).hom ≫
      torCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf n := by
  apply NatTrans.ext
  funext X
  let A := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let G' := largeTensorFunctorAt.{max z t, r, s, a, b} R S B'
  let ε := (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
    Rᵐᵒᵖ).hom.app X
  let α := largeTorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n
  let β := largeTorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf n
  let e := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app A
  let e' := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom.app A
  have hCore : V.map (α.app A) ≫ e' = e ≫ β.app (U.obj A) := by
    have h := congrArg (fun γ => γ.app A)
      (largeTorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf n)
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using h
  have hFlat : (G.leftDerived n).map ε ≫ β.app
        ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X) =
      β.app (U.obj A) ≫ (G'.leftDerived n).map ε := β.naturality ε
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [torHeightIsoAt_hom_app, torHeightIsoAt_hom_app]
  change V.map (α.app A) ≫ (e' ≫ (G'.leftDerived n).map ε) =
    (e ≫ (G.leftDerived n).map ε) ≫ β.app
      ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X)
  calc
    _ = (e ≫ β.app (U.obj A)) ≫ (G'.leftDerived n).map ε := by
      have h := congrArg (fun f => f ≫ (G'.leftDerived n).map ε) hCore
      exact (Category.assoc (V.map (α.app A)) e' ((G'.leftDerived n).map ε)).symm.trans h
    _ = _ := by
      have h := congrArg (fun f => e ≫ f) hFlat.symm
      exact (Category.assoc e (β.app (U.obj A)) ((G'.leftDerived n).map ε)).trans
        (h.trans (Category.assoc e ((G.leftDerived n).map ε)
          (β.app ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X))).symm)


end Heights

section SufficientOriginalWorld

universe vGlobal

local instance originalOppositeSmall (R : Type rGlobal) [Small.{vGlobal} R] :
    Small.{vGlobal} Rᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

variable (C : Type vGlobal) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
  [SMulCommClass R Sᵐᵒᵖ C] [Small.{vGlobal} R]

/-- Compare the original common-world native Tor only when that source really contains R.
No smallness or projective-resolution premise is imposed on the outer S-category. -/
def torOriginalLiftIsoAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] (n : ℕ) :
    torFunctor R S C n ⋙ ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ ≅
      torFunctorAt.{z, r, s, v, v} R S C n := by
  let F := tensorFunctor R S C
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S C
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso U V F G
    (tensorOriginalLiftIsoAt.{z, r, s, v} R S C) n


/-- The sufficient original-world comparison agrees with the actual degree-zero tensor map. -/
theorem torOriginalLiftIsoAt_hom_zero.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] :
    (torOriginalLiftIsoAt.{z, r, s, v} R S C 0).hom ≫
        (torZeroIsoAt.{z, r, s, v, v} R S C).hom ≫
          (tensorOriginalLiftIsoAt.{z, r, s, v} R S C).hom =
      Functor.whiskerRight (torZeroIso R S C).hom
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) := by
  let F := tensorFunctor R S C
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S C
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesProjectiveObjects := inferInstance
  let e := tensorOriginalLiftIsoAt.{z, r, s, v} R S C
  change (Functor.leftDerivedTransportIso U V F G e 0).hom ≫
    Functor.whiskerLeft U G.fromLeftDerivedZero ≫ e.hom = Functor.whiskerRight F.fromLeftDerivedZero V
  have h := congrArg (fun α => α ≫ e.hom)
    (Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero U V F G e)
  exact (Category.assoc (Functor.leftDerivedTransportIso U V F G e 0).hom
      (Functor.whiskerLeft U G.fromLeftDerivedZero) e.hom).symm.trans
    (h.trans ((Category.assoc (Functor.whiskerRight F.fromLeftDerivedZero V) e.inv e.hom).trans
      ((congrArg (fun α => Functor.whiskerRight F.fromLeftDerivedZero V ≫ α) e.inv_hom_id).trans
        (Category.comp_id _))))


end SufficientOriginalWorld

section CommonHeightCoherence

/-- Two actual working heights are compared in their explicitly common third height. -/
def torCommonHeightIsoAt.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ ≅
      torFunctorAt.{t, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ :=
  torHeightIsoAt.{max t u, z, r, s, a, b} R S B n ≪≫
    (torHeightIsoAt.{max z u, t, r, s, a, b} R S B n).symm

/-- The common-height tensor comparison uses the same actual input and coefficient lifts. -/
def tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ ≅
      tensorFunctorAt.{t, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ :=
  tensorHeightFacadeIsoAt.{max t u, z, r, s, a, b} R S B ≪≫
    (tensorHeightFacadeIsoAt.{max z u, t, r, s, a, b} R S B).symm

/-- Equal working heights give the identity using their actual common lift maps. -/
theorem torCommonHeightIsoAt_refl.{u, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCommonHeightIsoAt.{u, z, z, r, s, a, b} R S B n = Iso.refl _ := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id, Iso.refl_hom]

/-- Reversing the common-height Tor comparison gives its actual inverse. -/
theorem torCommonHeightIsoAt_symm.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    (torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n).symm =
      torCommonHeightIsoAt.{u, z, t, r, s, a, b} R S B n := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]

/-- Three working heights compose through the same earned maps to one common universe. -/
theorem torCommonHeightIsoAt_trans.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n ≪≫
        torCommonHeightIsoAt.{z, u, t, r, s, a, b} R S B n =
      torCommonHeightIsoAt.{t, u, z, r, s, a, b} R S B n := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The original tensor comparison has the same equal-height identity. -/
theorem tensorCommonHeightIsoAt_refl.{u, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCommonHeightIsoAt.{u, z, z, r, s, a, b} R S B = Iso.refl _ := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id, Iso.refl_hom]

/-- Reversing tensor working heights gives the same actual inverse. -/
theorem tensorCommonHeightIsoAt_symm.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B).symm =
      tensorCommonHeightIsoAt.{u, z, t, r, s, a, b} R S B := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]

/-- The tensor triangles commute on all three heights in their explicit common universe. -/
theorem tensorCommonHeightIsoAt_trans.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B ≪≫
        tensorCommonHeightIsoAt.{z, u, t, r, s, a, b} R S B =
      tensorCommonHeightIsoAt.{t, u, z, r, s, a, b} R S B := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- Common-height Tor triangles retain the actual degree-zero tensor endpoints. -/
theorem torCommonHeightIsoAt_hom_zero.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B 0).hom ≫
        Functor.whiskerRight (torZeroIsoAt.{t, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ) =
      Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ) ≫
        (tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B).hom := by
  let ez := torHeightIsoAt.{max t u, z, r, s, a, b} R S B 0
  let et := torHeightIsoAt.{max z u, t, r, s, a, b} R S B 0
  let qz := tensorHeightFacadeIsoAt.{max t u, z, r, s, a, b} R S B
  let qt := tensorHeightFacadeIsoAt.{max z u, t, r, s, a, b} R S B
  let az := Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
    (ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ)
  let augmentationT := Functor.whiskerRight (torZeroIsoAt.{t, r, s, a, b} R S B).hom
    (ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ)
  let ac := (torZeroIsoAt.{max z t u, r, s, a, b} R S B).hom
  have hz : ez.hom ≫ ac = az ≫ qz.hom := torHeightIsoAt_hom_zero R S B
  have ht : et.hom ≫ ac = augmentationT ≫ qt.hom := torHeightIsoAt_hom_zero R S B
  apply (cancel_mono qt.hom).1
  change ((ez.hom ≫ et.inv) ≫ augmentationT) ≫ qt.hom =
    (az ≫ (qz.hom ≫ qt.inv)) ≫ qt.hom
  calc
    _ = ez.hom ≫ et.inv ≫ (augmentationT ≫ qt.hom) := by simp only [Category.assoc]
    _ = ez.hom ≫ et.inv ≫ (et.hom ≫ ac) := congrArg (fun f => ez.hom ≫ et.inv ≫ f) ht.symm
    _ = ez.hom ≫ ac := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = az ≫ qz.hom := hz
    _ = _ := by
      symm
      calc
        (az ≫ (qz.hom ≫ qt.inv)) ≫ qt.hom =
            az ≫ (qz.hom ≫ (qt.inv ≫ qt.hom)) := by
          exact (Category.assoc az (qz.hom ≫ qt.inv) qt.hom).trans
            (congrArg (fun α => az ≫ α) (Category.assoc qz.hom qt.inv qt.hom))
        _ = az ≫ qz.hom := by
          rw [qt.inv_hom_id, Category.comp_id]

end CommonHeightCoherence

end ModuleCat.BalancedTensorRight
