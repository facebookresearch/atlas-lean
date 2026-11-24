/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathMaximumFlags

/-!
# The actual original path-to-maximum-flag comparison

The original path is included in its actual maximum flag, giving a
natural transformation on the whole original zero-to-last path category.
A concrete skipped-vertex path is not equal to its completed flag; the
section is not asserted to be a strict inverse.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.PathFlagComparison
open PathLastMaximum PathMaximumFlags
variable {n : ℕ}

/-- The actual inclusion of every original path into its complete maximum flag, natural on
all original
  path-poset arrows. -/
def completion : 𝟭 (LastPath.{u} (0 : Fin (n + 1))) ⟶
    maximumFunctor (0 : Fin (n + 1)) ⋙ flagFunctor.{u} where
  app p := ⟨homOfLE (path_le_flag p)⟩
  naturality p q f := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The comparison retains exactly the original path-to-flag subset inclusion at every
supplied path. -/
theorem completion_app (p : LastPath.{u} (0 : Fin (n + 1))) :
    (completion.{u}).app p = ⟨homOfLE (path_le_flag p)⟩ := rfl

/-- The actual original path skips front vertex one while retaining zero, front vertex two
and the last vertex three. -/
def skippedPath : LastPath.{u} (0 : Fin 3) where
  I := {ULift.up.{u} (0 : Fin 4), ULift.up.{u} (2 : Fin 4), ULift.up.{u} (3 : Fin 4)}
  left := by simp
  right := by simp
  left_le x _ := Fin.zero_le x.down
  le_right x _ := Fin.le_last x.down

/-- The retained original front vertex two is the maximum of the skipped path. -/
theorem skippedPath_maximum : maximum 0 (skippedPath.{u}) = (2 : Fin 3) := by
  apply le_antisymm
  · exact Fin.le_last _
  · apply le_maximum 0 (skippedPath.{u}) (2 : Fin 3)
    apply (mem_frontSet 0 (skippedPath.{u}) _).mpr
    simp only [skippedPath, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (Or.inl rfl)

/-- The same original skipped front vertex one belongs to the complete maximum flag. -/
theorem one_mem_maximum_flag : ULift.up.{u} (1 : Fin 4) ∈ (flag (maximum 0
  (skippedPath.{u}))).I := by
  rw [skippedPath_maximum]
  exact Or.inl (by change (1 : Fin 4) ≤ 2; decide)

/-- The original skipped vertex one does not belong to the original supplied path. -/
theorem one_not_mem_skippedPath : ULift.up.{u} (1 : Fin 4) ∉ (skippedPath.{u}).I := by
  simp only [skippedPath, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide

/-- The actual original path is not equal to its completed maximum flag; no strict inverse
follows from the
  flag section. -/
theorem skippedPath_ne_flag : skippedPath.{u} ≠ flag (maximum 0 (skippedPath.{u})) := by
  intro h
  exact one_not_mem_skippedPath (h ▸ one_mem_maximum_flag)

end CategoryTheory.CoherentRealization.PathFlagComparison
