/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeKanGenerators
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Actual small fixed-object boundary and horn families

The literal free maps are indexed by the original ordered pair and the
scalar dimension. These actual families are small and have precisely the
same right lifting classes as the isomorphism-closed free generators.
Smallness is asserted for the literal families, not their isomorphism
closures or a supplied model structure.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable (O : Type u)

/-- The actual free boundary family, including dimension zero and loop object pairs. -/
def boundaryFamily : MorphismProperty (FixedObjects O) :=
  .ofHoms (fun i : O × O × ℕ =>
    (FreeSingleHom.functor i.1 i.2.1).map (∂Δ[i.2.2]).ι)

/-- The actual free positive-dimensional horn family at every original ordered pair. -/
def hornFamily : MorphismProperty (FixedObjects O) :=
  .ofHoms (fun i : Σ n : ℕ, O × O × Fin (n + 2) =>
    (FreeSingleHom.functor i.2.1 i.2.2.1).map (Λ[i.1 + 1, i.2.2.2]).ι)

instance : MorphismProperty.IsSmall.{u} (boundaryFamily O) :=
  MorphismProperty.isSmall_ofHoms _

instance : MorphismProperty.IsSmall.{u} (hornFamily O) :=
  MorphismProperty.isSmall_ofHoms _

variable {O}

/-- Every original free boundary inclusion is a literal member of the small family. -/
theorem boundary_mem_family (x y : O) (n : ℕ) :
    boundaryFamily O ((FreeSingleHom.functor x y).map (∂Δ[n]).ι) := ⟨(x, y, n)⟩

/-- Every original positive-dimensional free horn is a literal member of the small family. -/
theorem horn_mem_family (x y : O) (n : ℕ) (i : Fin (n + 2)) :
    hornFamily O ((FreeSingleHom.functor x y).map (Λ[n + 1, i]).ι) :=
  ⟨(⟨n, x, y, i⟩ : Σ n : ℕ, O × O × Fin (n + 2))⟩

/-- The literal small boundary family detects exactly the original scalar boundary lifting problems. -/
theorem boundaryFamily_rlp_iff {C D : FixedObjects O} (p : C ⟶ D) :
    (boundaryFamily O).rlp p ↔ ∀ x y : O, SSet.modelCategoryQuillen.I.rlp (homMap p x y) := by
  constructor
  · intro h x y A B i hi
    obtain ⟨n⟩ := hi
    exact (hasLiftingProperty_free_iff x y _ p).mp
      (h _ (boundary_mem_family x y n))
  · intro h A B i hi
    obtain ⟨⟨x, y, n⟩⟩ := hi
    exact (hasLiftingProperty_free_iff x y _ p).mpr (h x y _ ⟨n⟩)

/-- The literal small horn family detects exactly the original scalar horn lifting problems. -/
theorem hornFamily_rlp_iff {C D : FixedObjects O} (p : C ⟶ D) :
    (hornFamily O).rlp p ↔ ∀ x y : O, SSet.modelCategoryQuillen.J.rlp (homMap p x y) := by
  constructor
  · intro h x y A B i hi
    obtain ⟨n, hi⟩ := (MorphismProperty.iSup_iff _ _).mp hi
    obtain ⟨j⟩ := hi
    exact (hasLiftingProperty_free_iff x y _ p).mp
      (h _ (horn_mem_family x y n j))
  · intro h A B i hi
    obtain ⟨⟨n, x, y, j⟩⟩ := hi
    exact (hasLiftingProperty_free_iff x y _ p).mpr
      (h x y _ ((MorphismProperty.iSup_iff _ _).mpr ⟨n, ⟨j⟩⟩))

/-- The actual small boundary family and the free isomorphism closure have the same right lifting class. -/
theorem boundaryFamily_rlp_eq : (boundaryFamily O).rlp = (boundaryGenerators (O := O)).rlp := by
  ext C D p
  exact (boundaryFamily_rlp_iff p).trans (freeGenerators_rlp_iff _ p).symm

/-- The actual small horn family and the free isomorphism closure have the same right lifting class. -/
theorem hornFamily_rlp_eq : (hornFamily O).rlp = (hornGenerators (O := O)).rlp := by
  ext C D p
  exact (hornFamily_rlp_iff p).trans (freeGenerators_rlp_iff _ p).symm

end CategoryTheory.SimplicialEnrichment.FixedObjects
