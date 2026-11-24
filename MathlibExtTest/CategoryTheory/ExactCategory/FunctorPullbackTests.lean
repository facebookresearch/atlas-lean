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

import MathlibExt.CategoryTheory.ExactCategory.Functor
import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Exact functors preserve admissible pullback squares

Focused consumers for
`Functor.map_isPullback_of_isAdmissibleMono_of_isAdmissibleEpi` in the
standard exact category `ModuleCat ℚ`. Split biproduct legs exercise a
nontrivial admissible mono and epi, while identity opposite legs give canonical
pullback squares.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

namespace MathlibExtTest.CategoryTheory.ExactCategory.FunctorPullbackTests

private theorem mappedInlPullback (X Y : ModuleCat ℚ) :
    IsPullback
      ((𝟭 (ModuleCat ℚ)).map (𝟙 X))
      ((𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y))
      ((𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y))
      ((𝟭 (ModuleCat ℚ)).map (𝟙 (X ⊞ Y))) := by
  have hSplit := ExactCategory.isAdmissibleExact_split X Y
  exact (𝟭 (ModuleCat ℚ)).map_isPullback_of_isAdmissibleMono_of_isAdmissibleEpi
    IsPullback.of_id_fst (ExactCategory.isAdmissibleMono_f hSplit)
      (ExactCategory.IsAdmissibleEpi.id _)

private theorem mappedSndPullback (X Y : ModuleCat ℚ) :
    IsPullback
      ((𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y))
      ((𝟭 (ModuleCat ℚ)).map (𝟙 (X ⊞ Y)))
      ((𝟭 (ModuleCat ℚ)).map (𝟙 Y))
      ((𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y)) := by
  have hSplit := ExactCategory.isAdmissibleExact_split X Y
  exact (𝟭 (ModuleCat ℚ)).map_isPullback_of_isAdmissibleMono_of_isAdmissibleEpi
    IsPullback.of_id_snd (ExactCategory.IsAdmissibleMono.id _)
      (ExactCategory.isAdmissibleEpi_g hSplit)

/-- The mapped split-mono square has the expected commutativity orientation. -/
example (X Y : ModuleCat ℚ) :
    (𝟭 (ModuleCat ℚ)).map (𝟙 X) ≫
        (𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y) =
      (𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y) ≫
        (𝟭 (ModuleCat ℚ)).map (𝟙 (X ⊞ Y)) :=
  (mappedInlPullback X Y).w

/-- The mapped split-epi square exposes its lift through the public pullback API. -/
noncomputable example (X Y : ModuleCat ℚ) :
    ∃ l : (𝟭 (ModuleCat ℚ)).obj (X ⊞ Y) ⟶ (𝟭 (ModuleCat ℚ)).obj (X ⊞ Y),
      l ≫ (𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y) =
          (𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y) ∧
        l ≫ (𝟭 (ModuleCat ℚ)).map (𝟙 (X ⊞ Y)) =
          (𝟭 (ModuleCat ℚ)).map (𝟙 (X ⊞ Y)) := by
  let h := mappedSndPullback X Y
  exact h.exists_lift _ _ h.w

end MathlibExtTest.CategoryTheory.ExactCategory.FunctorPullbackTests
