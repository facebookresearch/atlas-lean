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
# Original projective-dimension bounds from finite resolutions

If the resolving objects map to projective objects, the existing finite resolution is an
projective resolution in the original abelian target. Every Ext class in degree above its
inclusive bound has a representative whose source is an zero term, so that class vanishes.

This proves the original `HasProjectiveDimensionLE` bound by the existing Ext criterion, retaining
the original resolving complex, augmentation, support bound, and projective-resolution conversion.
Neither a dimension outcome nor a new resolution or dimension model is introduced.
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

/--
Every original Ext class strictly above the finite support bound vanishes because its
projective-resolution source term is zero.
-/
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

/--
An finite resolution by projectives yields the existing projective-dimension bound at its original
inclusive support bound.
-/
theorem hasProjectiveDimensionLE (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    HasProjectiveDimensionLE X Q.bound := by
  letI := HasExt.standard A
  apply HasProjectiveDimensionLT.mk
  intro n hn Y α
  exact ext_eq_zero_above Q hproj n (Nat.lt_of_succ_le hn) Y α

/--
Any larger supplied bound is an bound for the original projective dimension, derived from the same
finite resolution.
-/
theorem hasProjectiveDimensionLE_of_bound_le (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) (n : ℕ) (hn : Q.bound ≤ n) :
    HasProjectiveDimensionLE X n := by
  letI : HasProjectiveDimensionLE X Q.bound := Q.hasProjectiveDimensionLE hproj
  exact hasProjectiveDimensionLT_of_ge X (Q.bound + 1) (n + 1)
    (Nat.add_le_add_right hn 1)

/--
The original numeric projective dimension is bounded by the finite support recorded in the
unchanged resolution.
-/
theorem projectiveDimension_le_bound (Q : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    projectiveDimension X ≤ Q.bound :=
  (projectiveDimension_le_iff X Q.bound).mpr (Q.hasProjectiveDimensionLE hproj)

end CategoryTheory.Abelian.FiniteResolution

end
