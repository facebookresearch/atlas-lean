/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentFirstJointSplit
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagNormalization

/-!
# Actual original first-joint bounds and endpoint flags

An interior original first-flag joint strictly lowers both interval
dimensions. If there is no such joint, the complete original first flag
is exactly the two original endpoints; terminal-support normalization
retains that same full endpoint flag.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open TerminalFlag

namespace TerminalFlag

/-- The entire supported preimage of an endpoint-only original first flag retains the same endpoints. -/
theorem coefficient_first_endpoints {n : ℕ} {q : SimplexCategoryᵒᵖ}
    (p : (coefficientObject.{u} n).obj q)
    (hp : (p.obj 0).I = {ULift.up.{u} (0 : Fin (n + 1)), ULift.up.{u} (Fin.last n)}) :
    ((coefficient p).obj 0).I =
      {ULift.up.{u} (0 : Fin (dimension p + 1)), ULift.up.{u} (Fin.last (dimension p))} := by
  rw [coefficient_flags, hp]
  ext i
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((liftedEmbedding p).injective (h.trans (lifted_zero p).symm))
    · exact Or.inr ((liftedEmbedding p).injective (h.trans (lifted_last p).symm))
  · intro h
    rcases h with rfl | rfl
    · exact Or.inl (lifted_zero p)
    · exact Or.inr (lifted_last p)

end TerminalFlag

namespace FirstJoint

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The exact original dimension of the complete first interval bead. -/
theorem leftBead_dimension (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (leftBead b j hj).dimension = j.val := by
  change j.val - 0 = j.val
  omega

/-- The exact original dimension of the complete second interval bead. -/
theorem rightBead_dimension (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (rightBead b j hj).dimension = b.dimension - j.val := rfl

/-- Both full original interval beads strictly decrease at an actual interior joint. -/
theorem dimensions_lt (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I)
    (h₀ : j ≠ 0) (h₁ : j ≠ Fin.last b.dimension) :
    (leftBead b j hj).dimension < b.dimension ∧
      (rightBead b j hj).dimension < b.dimension := by
  have hz : j.val ≠ 0 := fun h => h₀ (Fin.ext h)
  have ht : j.val ≠ b.dimension := fun h => h₁ (Fin.ext h)
  have hlt := j.isLt
  rw [leftBead_dimension, rightBead_dimension]
  omega

/-- Without an interior original first-flag joint, the whole original first flag is exactly its endpoints. -/
theorem first_endpoints_of_no_interior (b : Bead K x y q)
    (h : ¬ ∃ j : Fin (b.dimension + 1),
      j ≠ 0 ∧ j ≠ Fin.last b.dimension ∧
        ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    ((originalCoefficient b).obj 0).I =
      {ULift.up.{u} (0 : Fin (b.dimension + 1)), ULift.up.{u} (Fin.last b.dimension)} := by
  ext i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hi
    by_cases hz : i.down = 0
    · exact Or.inl (ULift.ext hz)
    · by_cases ht : i.down = Fin.last b.dimension
      · exact Or.inr (ULift.ext ht)
      · exact False.elim (h ⟨i.down, hz, ht, hi⟩)
  · intro hi
    rcases hi with rfl | rfl
    · exact ((originalCoefficient b).obj 0).left
    · exact ((originalCoefficient b).obj 0).right

end FirstJoint

end CategoryTheory.CoherentRealization.OriginalBead
