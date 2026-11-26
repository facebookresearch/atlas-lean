/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.ProjectiveFlatTargetTensor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorAugmentation
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MathlibExt.Algebra.Homology.ChainComplexAugmentationHomology
public import MathlibExt.Algebra.Homology.ChainComplex.ToSingleHomologyZero

/-!
# Degree-zero homology of coefficient-tensored projective resolutions

Let R be a commutative ring in universe u, M an arbitrary coefficient R-module in universe v,
and P a projective resolution of an R-module X in universe max(u,w). Tensoring P with M gives
the chain complex M⊗_R P in coefficient universe W=max(u,v,w). Its augmentation to the single
complex on M⊗_R X induces the canonical isomorphism H_0(M⊗_R P)≅M⊗_R X. The degree-zero class
map followed by this isomorphism is id_M⊗π_0.

A copy M̃ of M placed in W has its canonical linear identification with M. Tensoring that
identification with each target module gives a natural isomorphism M̃⊗_R(-)≅M⊗_R(-), and
applying it termwise identifies the two coefficient tensor complexes. The coefficient M requires
no flatness assumption; the homology assertion is in degree zero.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

namespace ModuleCat

variable (R : Type u) [CommRing R]
  (M : ModuleCat.{v} R) {X : ModuleCat.{max u w} R}
  (P : ProjectiveResolution X)

/-- Let R be a commutative ring in universe u, M an R-module in universe v, X an R-module in
universe max(u,w), and P a projective resolution of X of shape down ℕ. Write W=max(u,v,w) for
the tensor coefficient universe. The tensor augmentation gives this isomorphism H_0(M⊗_R P)≅M⊗_R
X. Tensoring with the arbitrary coefficient M preserves cokernels, so the augmentation's
degree-zero presentation computes the tensor product without a flatness hypothesis on M. -/
def projectiveCoefficientHomologyZeroIso :
    (projectiveCoefficientComplex R M P).homology 0 ≅
      ((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X := by
  let F := (tensorBifunctorAt.{u, v, max u w} R).obj M
  let _ : PreservesFiniteColimits F := projectiveCoefficientTensor_preservesFiniteColimits R M
  exact ChainComplex.homologyZeroIsoOfPreservedAugmentation F P.π

/-- Let R be a commutative ring in universe u, M an R-module in universe v, X an R-module in
universe max(u,w), and P a projective resolution of X of shape down ℕ. Write W=max(u,v,w) for
the tensor coefficient universe. Let q_0:M⊗_R P_0→H_0(M⊗_R P) be the degree-zero homology class
map and e_0:H_0(M⊗_R P)≅M⊗_R X the tensor augmentation comparison. Then q_0≫e_0.hom=id_M⊗π_0,
where π_0:P_0→X is the resolution augmentation. -/
@[reassoc]
theorem projectiveCoefficientHomologyZeroIso_class :
    ChainComplex.homologyZeroClass (projectiveCoefficientComplex R M P) ≫
      (projectiveCoefficientHomologyZeroIso R M P).hom =
        ((tensorBifunctorAt.{u, v, max u w} R).obj M).map (P.π.f 0) := by
  let F := (tensorBifunctorAt.{u, v, max u w} R).obj M
  let _ : PreservesFiniteColimits F := projectiveCoefficientTensor_preservesFiniteColimits R M
  exact ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom F P.π

/-- Let R be a commutative ring in universe u, M an R-module in universe v, X an R-module in
universe max(u,w), and P a projective resolution of X of shape down ℕ. Write W=max(u,v,w) for
the tensor coefficient universe. Let a:M⊗_R P→(M⊗_R X)[0] be the tensor augmentation,
e_0:H_0(M⊗_R P)≅M⊗_R X its canonical comparison, and s:H_0((M⊗_R X)[0])≅M⊗_R X the
single-complex homology isomorphism. Then H_0(a)≫s.hom=e_0.hom. -/
@[reassoc]
theorem projectiveCoefficientAugmentation_homology_zero :
    HomologicalComplex.homologyMap (projectiveCoefficientAugmentation R M P) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0
        (((tensorBifunctorAt.{u, v, max u w} R).obj M).obj X)).hom =
      (projectiveCoefficientHomologyZeroIso R M P).hom := by
  apply Cofork.IsColimit.hom_ext
    (ChainComplex.homologyZeroCoforkIsColimit (projectiveCoefficientComplex R M P))
  exact (ChainComplex.homologyZeroClass_toSingle (projectiveCoefficientAugmentation R M P)).trans
    ((projectiveCoefficientAugmentation_f_zero R M P).trans
      (projectiveCoefficientHomologyZeroIso_class R M P).symm)

/-- Let R be a commutative ring in universe u and M an R-module in universe v, with an independent
target height w. This auxiliary R-module M̃ is a copy of M placed in W=max(u,v,w), with its
lifted R-action and canonical linear identification M̃≅M. It allows tensoring with target
modules in universe max(u,w) using the common coefficient universe. -/
def auxiliaryCoefficient : ModuleCat.{max u v w} R :=
  ModuleCat.of R (ULift.{max u w} M)

/-- Let R be commutative in universe u, M an R-module in universe v, and M̃ its canonical copy in
W=max(u,v,w). For target modules Y in universe max(u,w), the linear identification a:M̃≅M
induces a natural isomorphism M̃⊗_R Y≅M⊗_R Y by a⊗id_Y. Its forward map sends m̃⊗y to a(m̃)⊗y,
and the output tensors lie in W. -/
def coefficientUnliftNatIso :
    (tensorBifunctorAt.{u, max u v w, max u w} R).obj (auxiliaryCoefficient.{u, v, w} R M) ≅
      (tensorBifunctorAt.{u, v, max u w} R).obj M :=
  NatIso.ofComponents (fun Y =>
    (TensorProduct.congr (ULift.moduleEquiv : ULift.{max u w} M ≃ₗ[R] M)
      (LinearEquiv.refl R Y)).toModuleIso) (by
        intro Y Z g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro m y
        change m.down ⊗ₜ[R] g.hom y = m.down ⊗ₜ[R] g.hom y
        rfl)

/-- Let R be a commutative ring in universe u, M an R-module in universe v, X an R-module in
universe max(u,w), and P a projective resolution of X of shape down ℕ. Write W=max(u,v,w) for
the tensor coefficient universe. Let M̃ be the canonical copy of M in W with identification
a:M̃≅M. This chain isomorphism M̃⊗_R P≅M⊗_R P has component a⊗id_{P_n} in every degree n∈ℕ.
Naturality of the coefficient tensor comparison makes these components commute with every
differential of the resolution. -/
def coefficientUnliftComplexIso :
    ((((tensorBifunctorAt.{u, max u v w, max u w} R).obj (auxiliaryCoefficient.{u, v, w} R M)).mapHomologicalComplex
      (.down ℕ)).obj P.complex) ≅ projectiveCoefficientComplex R M P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientUnliftNatIso.{u, v, w} R M).app (P.complex.X n))
    (by
      intro i j _h
      exact ((coefficientUnliftNatIso.{u, v, w} R M).hom.naturality (P.complex.d i j)).symm)

end ModuleCat
