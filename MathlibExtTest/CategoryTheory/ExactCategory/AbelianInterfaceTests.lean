/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.CategoryTheory.ExactCategory.Bicartesian
import MathlibExt.CategoryTheory.ExactCategory.Functor
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Tests of the maximal exact structure on integer modules

The canonical Abelian instance supplies the exact structure on `ModuleCat ℤ`.
The split sequence `ℤ → ℤ ⊞ ℤ → ℤ` has nonzero inclusion and projection.
A triangular middle map with identity endpoints gives both a pullback and
a pushout. Exact identity functors preserve the sequence and these maps.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.ExactCategory

noncomputable section

namespace MathlibExtTest.CategoryTheory.ExactCategory.AbelianInterface

abbrev Z := ModuleCat.of ℤ ℤ

/-- The nonzero split exact sequence with first inclusion and second projection. -/
def S : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (biprod.inl : Z ⟶ Z ⊞ Z) biprod.snd (by simp)

/-- A triangular endomorphism of the middle module. -/
def middle : Z ⊞ Z ⟶ Z ⊞ Z :=
  biprod.lift (biprod.fst + biprod.snd) biprod.snd

/-- The endpoints are identities while the middle map adds the second coordinate to the first. -/
def shear : S ⟶ S where
  τ₁ := 𝟙 Z
  τ₂ := middle
  τ₃ := 𝟙 Z
  comm₁₂ := by
    apply biprod.hom_ext
    · simp [S, middle]
    · simp [S, middle]
  comm₂₃ := by simp [S, middle]

/-- Admissibility is derived from the split-sequence axiom of the inferred exact structure. -/
lemma admissible_S : IsAdmissibleExact S := isAdmissibleExact_split Z Z

/-- The priority-100 Abelian instance is available without an exact-category assumption. -/
example : ExactCategory (ModuleCat ℤ) := inferInstance

/-- The first nonzero inclusion is admissible. -/
example : IsAdmissibleMono (biprod.inl : Z ⟶ Z ⊞ Z) :=
  isAdmissibleMono_f admissible_S

/-- The second nonzero projection is admissible. -/
example : IsAdmissibleEpi (biprod.snd : Z ⊞ Z ⟶ Z) :=
  isAdmissibleEpi_g admissible_S

/-- The triangular map gives a pullback square on the final two terms. -/
example : IsPullback S.g middle (𝟙 Z) S.g := by
  let : IsIso shear.τ₁ := by change IsIso (𝟙 Z); infer_instance
  exact isPullback_g_of_isAdmissibleExact_of_isIso_left shear admissible_S admissible_S

/-- Its identity right endpoint gives a pushout square on the first two terms. -/
example : IsPushout S.f (𝟙 Z) middle S.f := by
  let : IsIso shear.τ₃ := by change IsIso (𝟙 Z); infer_instance
  exact isPushout_f_of_isAdmissibleExact_of_isIso_right shear admissible_S admissible_S

/-- Exactness of the identity functor is inferred. -/
example : (𝟭 (ModuleCat ℤ)).IsExact := inferInstance

/-- Applying the exact identity functor preserves the concrete admissible sequence. -/
example : IsAdmissibleExact (S.map (𝟭 (ModuleCat ℤ))) :=
  (𝟭 (ModuleCat ℤ)).map_admissibleExact S admissible_S

/-- The exact-functor pushout interface preserves the triangular square along its admissible inclusion. -/
example : IsPushout ((𝟭 (ModuleCat ℤ)).map (𝟙 Z))
    ((𝟭 (ModuleCat ℤ)).map S.f) ((𝟭 (ModuleCat ℤ)).map S.f)
    ((𝟭 (ModuleCat ℤ)).map middle) := by
  let : IsIso shear.τ₃ := by change IsIso (𝟙 Z); infer_instance
  have hpo : IsPushout S.f (𝟙 Z) middle S.f :=
    isPushout_f_of_isAdmissibleExact_of_isIso_right shear admissible_S admissible_S
  exact (𝟭 (ModuleCat ℤ)).map_isPushout_of_isAdmissibleMono hpo.flip
    (isAdmissibleMono_f admissible_S)

end MathlibExtTest.CategoryTheory.ExactCategory.AbelianInterface
