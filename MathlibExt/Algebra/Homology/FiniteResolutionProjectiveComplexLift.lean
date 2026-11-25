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
# Lifting projective complexes into finite resolutions

Let P be a preadditive category, A an abelian category, and i : P → A an additive functor whose
object images are projective. Let R be a finite resolution of Z relative to i. For a
natural-number-indexed chain complex K of projective objects of A, an augmentation ε : K → Y[0],
and a map f : Y → Z, there is a chain map g : K → i(R) with g ≫ ε_R = ε ≫ f[0]. Neither
exactness nor boundedness of K is required.
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

/-- Let P be preadditive, A abelian, and i : P → A additive, with every i(P₀) projective. Let K be a
natural-number-indexed chain complex of projective objects, ε : K → Y[0] an augmentation, R a
finite resolution of Z relative to i, and f : Y → Z. Then liftFromProjectiveComplex gives a
chain map g : K → R.mappedComplex lifting f along the resolution augmentation. The source K may
be unbounded and need not resolve Y. -/
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

/-- Let P be preadditive, A abelian, and i : P → A additive with projective object images. Given a
complex K with projective terms, an augmentation ε : K → Y[0], a finite resolution R of Z, and f
: Y → Z, the lift g : K → R.mappedComplex satisfies g₀ ≫ ε_R,₀ = ε₀ ≫ f. Here ε_R is the
augmentation of R. -/
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

/-- Let P be preadditive, A abelian, and i : P → A additive with projective object images. For an
augmented natural-number-indexed complex ε : K → Y[0] of projective objects, a finite resolution
R of Z relative to i, and f : Y → Z, the lifted chain map g satisfies g ≫ ε_R = ε ≫ f[0] as maps
K → Z[0]. -/
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
