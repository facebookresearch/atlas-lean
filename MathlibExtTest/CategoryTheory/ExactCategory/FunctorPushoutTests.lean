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
# Exact functors preserve admissible pushout squares

Focused consumers for exact-functor preservation of admissible pushout
squares. Generic clients pin the arbitrary first leg and independent source
and target universes. In the standard exact category `ModuleCat ℚ`, split
biproduct legs separately exercise a nontrivial admissible mono and epi,
while identity opposite legs give canonical pushout squares.
-/

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.ExactCategory.FunctorPushoutTests

section General

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Exact functors preserve the reviewed pushout orientation with an
arbitrary first source leg and an admissible-mono second source leg. -/
example {X Y X' P : C} {i : X ⟶ Y} {f : X ⟶ X'}
    {inl : X' ⟶ P} {inr : Y ⟶ P}
    (hpo : IsPushout f i inl inr) (hi : IsAdmissibleMono i) :
    IsPushout (F.map f) (F.map i) (F.map inl) (F.map inr) :=
  F.map_isPushout_of_isAdmissibleMono hpo hi

/-- The mapped square retains the source-first commutativity orientation. -/
example {X Y X' P : C} {i : X ⟶ Y} {f : X ⟶ X'}
    {inl : X' ⟶ P} {inr : Y ⟶ P}
    (hpo : IsPushout f i inl inr) (hi : IsAdmissibleMono i) :
    F.map f ≫ F.map inl = F.map i ≫ F.map inr :=
  (F.map_isPushout_of_isAdmissibleMono hpo hi).w

/-- The identity functor maps a pushout along an identity admissible mono;
the arbitrary leg is not required to be an admissible epi. -/
example {X Y : C} (f : X ⟶ Y) :
    IsPushout ((𝟭 C).map f) ((𝟭 C).map (𝟙 X))
      ((𝟭 C).map (𝟙 Y)) ((𝟭 C).map f) :=
  (𝟭 C).map_isPushout_of_isAdmissibleMono
    IsPushout.of_id_snd (IsAdmissibleMono.id X)

section Negative

variable {X Y X' P : C} {i : X ⟶ Y} {f : X ⟶ X'}
  {inl : X' ⟶ P} {inr : Y ⟶ P}

#guard_msgs (error, substring := true) in
#synth PreservesColimit (span f i) F

#guard_msgs (error, substring := true) in
example (hpo : IsPushout f i inl inr) :
    IsPushout (F.map f) (F.map i) (F.map inl) (F.map inr) :=
  F.map_isPushout hpo

end Negative

end General

private abbrev moduleId (X : ModuleCat ℚ) : X ⟶ X :=
  @CategoryStruct.id (ModuleCat ℚ) _ X

private theorem mappedInlPushout (X Y : ModuleCat ℚ) :
    IsPushout
      ((𝟭 (ModuleCat ℚ)).map (moduleId X))
      ((𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y))
      ((𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y))
      ((𝟭 (ModuleCat ℚ)).map (moduleId (X ⊞ Y))) := by
  have hSplit := ExactCategory.isAdmissibleExact_split X Y
  exact
    (𝟭 (ModuleCat ℚ)).map_isPushout_of_isAdmissibleEpi_of_isAdmissibleMono
      IsPushout.of_id_fst (ExactCategory.IsAdmissibleEpi.id _)
        (ExactCategory.isAdmissibleMono_f hSplit)

private theorem mappedSndPushout (X Y : ModuleCat ℚ) :
    IsPushout
      ((𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y))
      ((𝟭 (ModuleCat ℚ)).map (moduleId (X ⊞ Y)))
      ((𝟭 (ModuleCat ℚ)).map (moduleId Y))
      ((𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y)) := by
  have hSplit := ExactCategory.isAdmissibleExact_split X Y
  exact
    (𝟭 (ModuleCat ℚ)).map_isPushout_of_isAdmissibleEpi_of_isAdmissibleMono
      IsPushout.of_id_snd (ExactCategory.isAdmissibleEpi_g hSplit)
        (ExactCategory.IsAdmissibleMono.id _)

/-- The mapped split-mono square has the expected commutativity orientation. -/
example (X Y : ModuleCat ℚ) :
    (𝟭 (ModuleCat ℚ)).map (moduleId X) ≫
        (𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y) =
      (𝟭 (ModuleCat ℚ)).map (biprod.inl : X ⟶ X ⊞ Y) ≫
        (𝟭 (ModuleCat ℚ)).map (moduleId (X ⊞ Y)) :=
  (mappedInlPushout X Y).w

/-- The mapped split-epi square exposes its descent through the public pushout API. -/
noncomputable example (X Y : ModuleCat ℚ) :
    ∃ d : (𝟭 (ModuleCat ℚ)).obj Y ⟶ (𝟭 (ModuleCat ℚ)).obj Y,
      (𝟭 (ModuleCat ℚ)).map (moduleId Y) ≫ d =
          (𝟭 (ModuleCat ℚ)).map (moduleId Y) ∧
        (𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y) ≫ d =
          (𝟭 (ModuleCat ℚ)).map (biprod.snd : X ⊞ Y ⟶ Y) := by
  let h := mappedSndPushout X Y
  exact h.exists_desc _ _ h.w

#print axioms CategoryTheory.Functor.map_isPushout_of_isAdmissibleMono

end MathlibExtTest.CategoryTheory.ExactCategory.FunctorPushoutTests
