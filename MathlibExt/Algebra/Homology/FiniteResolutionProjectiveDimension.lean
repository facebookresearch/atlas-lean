/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionComparison
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective-dimension bounds from finite resolutions

Let P be preadditive, A abelian, and i : P → A additive with projective object images. A finite
resolution Q of X relative to i, supported through its inclusive natural-number bound b, gives
Extⁿ_A(X,Y) = 0 for every object Y and n > b. Consequently X has projective dimension at most b,
and every larger natural number is also a projective-dimension bound.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive] {X : A}

/-- Let P be preadditive, A abelian, and i : P → A additive with every object image projective. If Q
is a finite resolution of X relative to i and n is a natural number with Q.bound < n, then every
class α ∈ Extⁿ_A(X,Y) is zero, for every object Y of A. The Ext groups are the standard Ext
groups of the abelian category A. -/
theorem ext_eq_zero_above (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (n : ℕ) (hn : Q.bound < n) :
    letI := HasExt.standard A
    ∀ (Y : A) (α : Ext X Y n), α = 0 := by
  letI := HasExt.standard A
  intro Y α
  let R := Q.toProjectiveResolution hproj
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
  have hZero : IsZero (R.complex.X n) := by
    change IsZero (Q.mappedComplex.X n)
    exact Q.mappedComplex_isZero_above n hn
  have hf0 : f = 0 := hZero.eq_of_src f 0
  subst f
  exact R.extMk_zero (n + 1) rfl

/-- Let P be preadditive, A abelian, and i : P → A additive with projective object images. A finite
resolution Q of X relative to i implies that X has projective dimension at most Q.bound, the
inclusive bound on the nonzero terms of its resolving complex. -/
theorem hasProjectiveDimensionLE (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    HasProjectiveDimensionLE X Q.bound := by
  letI := HasExt.standard A
  apply HasProjectiveDimensionLT.mk
  intro n hn Y α
  exact ext_eq_zero_above Q hproj n (Nat.lt_of_succ_le hn) Y α

/-- Let P be preadditive, A abelian, and i : P → A additive with projective object images. If Q is a
finite resolution of X and n is a natural number satisfying Q.bound ≤ n, then X has projective
dimension at most n. -/
theorem hasProjectiveDimensionLE_of_bound_le (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (n : ℕ) (hn : Q.bound ≤ n) :
    HasProjectiveDimensionLE X n := by
  letI : HasProjectiveDimensionLE X Q.bound := Q.hasProjectiveDimensionLE hproj
  exact hasProjectiveDimensionLT_of_ge X (Q.bound + 1) (n + 1)
    (Nat.add_le_add_right hn 1)

/-- Let P be preadditive, A abelian, and i : P → A additive with every i(P₀) projective. For a
finite resolution Q of X relative to i, the numerical projective dimension satisfies
projectiveDimension(X) ≤ Q.bound, with the natural-number bound viewed in the ordered dimension
range. -/
theorem projectiveDimension_le_bound (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    projectiveDimension X ≤ Q.bound :=
  (projectiveDimension_le_iff X Q.bound).mpr (Q.hasProjectiveDimensionLE hproj)

end CategoryTheory.Abelian.FiniteResolution

end
