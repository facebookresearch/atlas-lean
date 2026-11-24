/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.FiniteResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.Projective.ComplexLift

/-!
# Lifting projective complexes to finite resolutions

An augmented complex of projective objects maps to the mapped complex of a
finite resolution whenever the resolving objects map to projectives. This is
a target-side wrapper around
`CategoryTheory.ProjectiveResolution.liftFromComplex`; the source need not be
exact or bounded.

## Main declarations

* `CategoryTheory.Abelian.FiniteResolution.liftFromProjectiveComplex`
* `CategoryTheory.Abelian.FiniteResolution.liftFromProjectiveComplex_f_zero_comp`
* `CategoryTheory.Abelian.FiniteResolution.liftFromProjectiveComplex_commutes`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe vP uP vA uA

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]
variable {Y Z : A}

/-- Lift an augmented complex of projective objects into a finite resolution
whose resolving objects map to projectives. -/
@[no_expose]
def liftFromProjectiveComplex
    (K : ChainComplex A ℕ)
    (ε : K ⟶ (ChainComplex.single₀ A).obj Y)
    (hK : ∀ n, Projective (K.X n))
    (R : FiniteResolution i Z)
    (f : Y ⟶ Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    K ⟶ R.mappedComplex :=
  ProjectiveResolution.liftFromComplex f K ε
    (R.toProjectiveResolution hproj) hK

/-- The degree-zero component of `liftFromProjectiveComplex` has the expected
augmentation factorization. -/
@[reassoc (attr := simp)]
theorem liftFromProjectiveComplex_f_zero_comp
    (K : ChainComplex A ℕ)
    (ε : K ⟶ (ChainComplex.single₀ A).obj Y)
    (hK : ∀ n, Projective (K.X n))
    (R : FiniteResolution i Z)
    (f : Y ⟶ Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (liftFromProjectiveComplex K ε hK R f hproj).f 0 ≫
        R.augmentation.f 0 =
      ε.f 0 ≫ f := by
  exact ProjectiveResolution.liftFromComplex_f_zero_comp f K ε
    (R.toProjectiveResolution hproj) hK

/-- The lifted chain map commutes with the source and finite-resolution
augmentations. -/
@[reassoc (attr := simp)]
theorem liftFromProjectiveComplex_commutes
    (K : ChainComplex A ℕ)
    (ε : K ⟶ (ChainComplex.single₀ A).obj Y)
    (hK : ∀ n, Projective (K.X n))
    (R : FiniteResolution i Z)
    (f : Y ⟶ Z)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    liftFromProjectiveComplex K ε hK R f hproj ≫ R.augmentation =
      ε ≫ (ChainComplex.single₀ A).map f := by
  exact ProjectiveResolution.liftFromComplex_commutes f K ε
    (R.toProjectiveResolution hproj) hK

end CategoryTheory.Abelian.FiniteResolution
