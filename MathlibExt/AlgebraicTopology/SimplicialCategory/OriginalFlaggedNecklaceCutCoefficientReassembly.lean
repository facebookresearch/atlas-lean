/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCuts
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientFunctor

/-!
# SAME complete original cut coefficient reassembly

Both entire original native cut flag preimages reassemble to the SAME
complete original flag under the actual original reassembly operator.
Every scalar flag and all original vertices are retained literally.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects

open SSet.OriginalNecklace OriginalBeadInterval
open OriginalBead.TerminalFlag (coefficientObject)

/-- Both full native original interval images cover the SAME original set of coefficient vertices. -/
theorem flag_preimage_union (T : Data) (j : Fin (T.dimension + 1))
    (S : Set (ULift.{u} (Fin (T.dimension + 1)))) :
    liftedEmbedding 0 j (Fin.zero_le j) '' (liftedEmbedding 0 j (Fin.zero_le j) ⁻¹' S) ∪
      liftedEmbedding j (Fin.last T.dimension) (Fin.le_last j) ''
        (liftedEmbedding j (Fin.last T.dimension) (Fin.le_last j) ⁻¹' S) = S := by
  ext k
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> exact hi
  · intro hk
    by_cases hj : k.down ≤ j
    · obtain ⟨i, hi⟩ := coverage 0 j (Fin.zero_le j) k
        (by rw [lifted_zero]; exact Fin.zero_le _) (by rw [lifted_last]; exact hj)
      exact Or.inl ⟨i, (congrArg (fun x => x ∈ S) hi).mpr hk, hi⟩
    · obtain ⟨i, hi⟩ := coverage j (Fin.last T.dimension) (Fin.le_last j) k
        (by rw [lifted_zero]; exact (not_le.mp hj).le) (by rw [lifted_last]; exact Fin.le_last _)
      exact Or.inr ⟨i, (congrArg (fun x => x ∈ S) hi).mpr hk, hi⟩

private instance {n : ℕ} (a b : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Both SAME whole original cut coefficients reassemble to the entire original coefficient. -/
theorem reassembly_coefficient (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    (coefficientFunctor.{u}.map (Cut.reassemblyMorphism T.necklace j hj)).app q
      (ConcatFlags.coefficient (leftCoefficient T j hj) (rightCoefficient T j hj)) = T.coefficient := by
  refine CategoryTheory.Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    let α := (Cut.reassemblyOperator T.necklace j hj).toOrderHom.uliftMap
    have hleft : α '' (ConcatFlags.prefixLift (length 0 j) (length j (Fin.last T.necklace.dimension)) ''
        ((leftCoefficient T j hj).obj t).I) =
      liftedEmbedding 0 j (Fin.zero_le j) '' ((leftCoefficient T j hj).obj t).I := by
      rw [Set.image_image]
      congr 1
      funext i
      apply ULift.ext
      exact Cut.reassembly_prefix T.necklace j hj i.down
    have hright : α '' (ConcatFlags.suffixLift (length 0 j) (length j (Fin.last T.necklace.dimension)) ''
        ((rightCoefficient T j hj).obj t).I) =
      liftedEmbedding j (Fin.last T.necklace.dimension) (Fin.le_last j) ''
        ((rightCoefficient T j hj).obj t).I := by
      rw [Set.image_image]
      congr 1
    change α '' (ConcatFlags.prefixLift (length 0 j) (length j (Fin.last T.necklace.dimension)) ''
      ((leftCoefficient T j hj).obj t).I ∪
        ConcatFlags.suffixLift (length 0 j) (length j (Fin.last T.necklace.dimension)) ''
          ((rightCoefficient T j hj).obj t).I) = (T.coefficient.obj t).I
    rw [Set.image_union, hleft, hright, leftCoefficient_flags, rightCoefficient_flags]
    exact flag_preimage_union T.necklace j (T.coefficient.obj t).I
  · intro i k f
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.CutObjects
