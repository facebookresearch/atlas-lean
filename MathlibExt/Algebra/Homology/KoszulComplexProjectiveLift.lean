/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.FiniteResolutionProjectiveComplexLift
public import MathlibExt.Algebra.Homology.KoszulComplexFamily

/-!
# Lifting a finite-family Koszul augmentation to resolutions

For a finite family a : I → R, the Koszul complex has projective terms and a quotient
augmentation with target the displayed universe lift of R/(a). A map from this augmentation
target to Z lifts to a chain map into any projective resolution of Z.

The same construction applies to a finite resolution through an additive functor whose images
are projective. The lift commutes with the augmentations in degree zero and as a map to the
single-degree complex. The family index, coefficient ring and resolving-category universe
levels remain as stated.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v vP uP

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable {I : Type v} [Fintype I]

/-- The lifted quotient target of a finite-family Koszul augmentation.

Use the coefficient module ULift(R modulo the family ideal) at height max(u,v). -/
abbrev familyAugmentationTarget (a : I → R) :
    ModuleCat.{max u v} R :=
  ModuleCat.of R
    (ULift.{max u v, u}
      (R ⧸ ideal R (I → R) (familyFunctional R a)))

/-- The comparison map from a Koszul family to a projective resolution.

For a map q from the quotient augmentation target to Z, projectivity of the Koszul terms gives
a chain map to the supplied projective resolution of Z. -/
@[no_expose]
def familyLiftToProjectiveResolution
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : ProjectiveResolution Z) :
    familyComplex R a ⟶ Q.complex :=
  ProjectiveResolution.liftFromComplex q
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a)) Q
    (familyComplex_projective R a)

/-- The projective-resolution lift commutes with degree-zero augmentation.

Its degree-zero map followed by the target augmentation equals the Koszul augmentation
followed by q. -/
@[reassoc (attr := simp)]
theorem familyLiftToProjectiveResolution_f_zero_comp
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : ProjectiveResolution Z) :
    (familyLiftToProjectiveResolution R a q Q).f 0 ≫ Q.π.f 0 =
      (augmentation R (I → R) (familyFunctional R a)).f 0 ≫ q := by
  exact ProjectiveResolution.liftFromComplex_f_zero_comp q
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a)) Q
    (familyComplex_projective R a)

/-- The projective-resolution lift commutes with the full augmentation.

The chain comparison followed by the target resolution map equals the Koszul augmentation
followed by the single-degree map of q. -/
@[reassoc (attr := simp)]
theorem familyLiftToProjectiveResolution_commutes
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : ProjectiveResolution Z) :
    familyLiftToProjectiveResolution R a q Q ≫ Q.π =
      augmentation R (I → R) (familyFunctional R a) ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map q := by
  exact ProjectiveResolution.liftFromComplex_commutes q
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a)) Q
    (familyComplex_projective R a)

/-- The comparison map to a finite resolution with projective images.

For additive i and projectivity of every i(P₀), lift q from the Koszul quotient target to the
mapped complex of the finite resolution. -/
@[no_expose]
def familyLiftToFiniteResolution
    {P : Type uP} [Category.{vP} P] [Preadditive P]
    (i : P ⥤ ModuleCat.{max u v} R) [i.Additive]
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : CategoryTheory.Abelian.FiniteResolution i Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    familyComplex R a ⟶ Q.mappedComplex :=
  Q.liftFromProjectiveComplex
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a))
    (familyComplex_projective R a) q hproj

/-- The finite-resolution lift commutes with degree-zero augmentation.

The degree-zero comparison followed by the finite-resolution augmentation equals the Koszul
augmentation followed by q. -/
@[reassoc (attr := simp)]
theorem familyLiftToFiniteResolution_f_zero_comp
    {P : Type uP} [Category.{vP} P] [Preadditive P]
    (i : P ⥤ ModuleCat.{max u v} R) [i.Additive]
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : CategoryTheory.Abelian.FiniteResolution i Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (familyLiftToFiniteResolution R i a q Q hproj).f 0 ≫
        Q.augmentation.f 0 =
      (augmentation R (I → R) (familyFunctional R a)).f 0 ≫ q := by
  exact Q.liftFromProjectiveComplex_f_zero_comp
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a))
    (familyComplex_projective R a) q hproj

/-- The finite-resolution lift commutes with the full augmentation.

The comparison into the mapped finite resolution satisfies the augmentation square with the
single-degree map induced by q. -/
@[reassoc (attr := simp)]
theorem familyLiftToFiniteResolution_commutes
    {P : Type uP} [Category.{vP} P] [Preadditive P]
    (i : P ⥤ ModuleCat.{max u v} R) [i.Additive]
    (a : I → R)
    {Z : ModuleCat.{max u v} R}
    (q : familyAugmentationTarget R a ⟶ Z)
    (Q : CategoryTheory.Abelian.FiniteResolution i Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    familyLiftToFiniteResolution R i a q Q hproj ≫ Q.augmentation =
      augmentation R (I → R) (familyFunctional R a) ≫
        (ChainComplex.single₀ (ModuleCat.{max u v} R)).map q := by
  exact Q.liftFromProjectiveComplex_commutes
    (familyComplex R a)
    (augmentation R (I → R) (familyFunctional R a))
    (familyComplex_projective R a) q hproj

end KoszulComplex
