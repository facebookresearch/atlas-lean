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
# Lifting finite-family Koszul complexes to projective resolutions

The Koszul complex of a finite family is termwise projective, so its quotient
augmentation admits a comparison map to any supplied projective resolution,
or to a finite resolution whose resolving objects map to projectives.

These maps require only a morphism from the universe-lifted family quotient
to the object resolved by the target. No regularity, positive-degree
exactness, base change, minimality, or residue-field injectivity is asserted.

## Main declarations

* `KoszulComplex.familyAugmentationTarget`
* `KoszulComplex.familyLiftToProjectiveResolution`
* `KoszulComplex.familyLiftToFiniteResolution`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v vP uP

namespace KoszulComplex

variable (R : Type u) [CommRing R]
variable {I : Type v} [Fintype I]

/-- The object concentrated in degree zero in the Koszul-family
augmentation. -/
abbrev familyAugmentationTarget (a : I → R) :
    ModuleCat.{max u v} R :=
  ModuleCat.of R
    (ULift.{max u v, u}
      (R ⧸ ideal R (I → R) (familyFunctional R a)))

/-- Lift the augmentation of a finite-family Koszul complex to a supplied
projective resolution after choosing a map from the quotient target to the
resolved object. -/
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

/-- The degree-zero component of the Koszul-family comparison has the
expected augmentation factorization. -/
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

/-- The Koszul-family comparison commutes with the quotient and target
augmentations. -/
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

/-- Finite-resolution target form of the Koszul-family comparison map. -/
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

/-- The degree-zero component of the finite-resolution comparison has the
expected augmentation factorization. -/
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

/-- The finite-resolution comparison commutes with the quotient and target
augmentations. -/
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
