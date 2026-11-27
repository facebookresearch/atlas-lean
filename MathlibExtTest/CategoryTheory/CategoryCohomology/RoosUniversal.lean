/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.CategoryCohomology.RoosUniversal

/-!
# Cofree effacement and universal Roos clients

The clients use the cofree unit to efface positive-degree Roos cohomology and
apply the resulting universal cohomological δ-functor.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.CategoryCohomology

universe v₁ v₂ u₁ u₂

namespace RoosUniversalTests

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A]

/-- Any actual coefficient map followed by the cofree unit dies in positive degree. -/
example {M N : I ⥤ A} (f : M ⟶ N) (n : ℕ) :
    ((roosCohomologicalDeltaFunctor (I := I) (A := A)).T (n + 1)).map
      (f ≫ (discreteCofreeUnit (I := I) A).app N) = 0 := by
  rw [Functor.map_comp, roosCohomologicalDeltaFunctor_map_cofreeUnit, comp_zero]

/-- Identity in degree zero determines an actual endomorphism in all degrees. -/
example (g : roosCohomologicalDeltaFunctor (I := I) (A := A) ⟶
    roosCohomologicalDeltaFunctor (I := I) (A := A))
    (hg : CohomologicalDeltaFunctor.Hom.app g 0 = 𝟙 _) : g = 𝟙 _ := by
  obtain ⟨k, hk, huniq⟩ := roosCohomologicalDeltaFunctor_isUniversal (I := I) (A := A)
    (roosCohomologicalDeltaFunctor (I := I) (A := A)) (𝟙 _)
  have h₁ : g = k := huniq g hg
  have h₂ : 𝟙 (roosCohomologicalDeltaFunctor (I := I) (A := A)) = k :=
    huniq (𝟙 _) (by
      change CohomologicalDeltaFunctor.Hom.app (𝟙 _) 0 = 𝟙 _
      rw [CohomologicalDeltaFunctor.Hom.id_app])
  exact h₁.trans h₂.symm

end RoosUniversalTests

end
