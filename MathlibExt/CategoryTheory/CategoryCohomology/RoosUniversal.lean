/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosDeltaFunctor
public import MathlibExt.CategoryTheory.CategoryCohomology.RoosCofreeContraction
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Cofree effacement and universality of Roos cohomology

Sized exact products in an abelian coefficient category give a cohomological
Roos δ-functor. The cofree unit is monic, and the contraction of the cofree
Roos complex effaces every positive degree. This proves universality through
the effacement criterion, without requiring injective resolutions or limits
of the coefficient diagrams.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A]
  [HasProducts.{max u₁ v₁} A] [AB4StarOfSize.{max u₁ v₁} A]

/-- The positive Roos degree sends the cofree unit to zero. -/
theorem roosCohomologicalDeltaFunctor_map_cofreeUnit (n : ℕ) (M : I ⥤ A) :
    ((roosCohomologicalDeltaFunctor (I := I) (A := A)).T (n + 1)).map
      ((discreteCofreeUnit (I := I) A).app M) = 0 := by
  let : ∀ i : I, HasProductsOfShape (discreteCofreeIndex i) A := fun _ ↦ inferInstance
  let : ∀ V : Discrete I ⥤ A,
      Functor.HasPointwiseRightKanExtension (discreteCofreeInclusion I) V :=
    fun V ↦ discreteCofreeHasPointwiseRightKanExtension A V
  let : ∀ V : Discrete I ⥤ A,
      Functor.HasRightKanExtension (discreteCofreeInclusion I) V := fun _ ↦ inferInstance
  let V := (discreteCofreeRestriction (I := I) A).obj M
  have hz : IsZero (((roosCohomologicalDeltaFunctor (I := I) (A := A)).T (n + 1)).obj
      ((discreteCofreeFunctor (I := I) A).obj V)) :=
    (isZero_roosCofree_homology_succ V n).of_iso
      ((roosDeltaFunctorHomologyIso (I := I) (A := A) (n + 1)).app
        ((discreteCofreeFunctor (I := I) A).obj V))
  exact hz.eq_zero_of_tgt _

/-- Every positive degree is effaced by that same cofree unit. -/
theorem roosCohomologicalDeltaFunctor_isEffaceable_succ (n : ℕ) :
    ((roosCohomologicalDeltaFunctor (I := I) (A := A)).T (n + 1)).IsEffaceable := by
  intro M
  refine ⟨(discreteCofreeFunctor (I := I) A).obj
      ((discreteCofreeRestriction (I := I) A).obj M),
    (discreteCofreeUnit (I := I) A).app M, ?_,
    roosCohomologicalDeltaFunctor_map_cofreeUnit n M⟩
  change Mono (((discreteCofreeInclusion I).ranAdjunction A).unit.app M)
  infer_instance

/-- The Roos δ-functor is universal without an enough-injectives hypothesis. -/
theorem roosCohomologicalDeltaFunctor_isUniversal :
    CohomologicalDeltaFunctor.IsUniversal (I ⥤ A) A
      (roosCohomologicalDeltaFunctor (I := I) (A := A)) :=
  CohomologicalDeltaFunctor.isUniversal_of_effaceable
    (roosCohomologicalDeltaFunctor (I := I) (A := A))
    (fun n ↦ roosCohomologicalDeltaFunctor_isEffaceable_succ n)

end CategoryTheory.CategoryCohomology

end
