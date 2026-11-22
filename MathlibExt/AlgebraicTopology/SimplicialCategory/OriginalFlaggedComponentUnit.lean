/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentConcatenation

/-!
# The SAME original zero-sided component unit maps

The full native suffix and prefix maps insert the original zero necklace.
Their complete original input and coefficient equations give genuine
flagged maps and the actual left/right component unit laws in all arities.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts

private instance {n : ℕ} (a b : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The full original suffix inserts the SAME zero-length source necklace. -/
def leftUnitNecklace (T : Object K x y q) :
    T.necklace ⟶ (concat (unit K q x) T).necklace where
  operator := suffixOperator 0 T.necklace.dimension
  source := Fin.ext rfl
  target := rfl
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact (suffix_mem_concat_iff Point.data T.necklace s).mpr hs

/-- The SAME original zero-sided native map is literally the complete suffix inclusion. -/
theorem leftUnitNecklace_map (T : Object K x y q) :
    (leftUnitNecklace T).map.{u} = concatRight (unit K q x).necklace T.necklace := by
  apply (cancel_mono (complex (concat (unit K q x) T).necklace.joints).ι).1
  rw [Morphism.map_ι, concatRight_ι]
  rfl

/-- Every whole original flag is retained by the SAME native left-unit map. -/
theorem leftUnitNecklace_flags (T : Object K x y q) :
    (OriginalBead.OuterOperator.map (leftUnitNecklace T).operator
      (leftUnitNecklace T).source (leftUnitNecklace T).target).app q T.coefficient =
        (concat (unit K q x) T).coefficient := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    change ConcatFlags.suffixLift 0 T.necklace.dimension '' (T.coefficient.obj t).I =
      ConcatFlags.prefixLift 0 T.necklace.dimension '' ((Point.pointCoefficient q).obj t).I ∪
        ConcatFlags.suffixLift 0 T.necklace.dimension '' (T.coefficient.obj t).I
    ext i
    constructor
    · exact Or.inr
    · rintro (hi | hi)
      · obtain ⟨j, _hj, rfl⟩ := hi
        have hj : j = ULift.up.{u} (0 : Fin 1) := @Subsingleton.elim (ULift.{u} (Fin 1)) inferInstance j _
        subst j
        exact ⟨ULift.up.{u} 0, (T.coefficient.obj t).left, ULift.ext (Fin.ext rfl)⟩
      · exact hi
  · intro i j f
    exact Subsingleton.elim _ _

/-- The actual full flagged map inserting the SAME original source unit. -/
def leftUnitMap (T : Object K x y q) : T ⟶ concat (unit K q x) T where
  necklaceMap := leftUnitNecklace T
  over := by
    rw [leftUnitNecklace_map]
    exact concat_second_input (unit K q x) T
  flags := leftUnitNecklace_flags T

/-- The full original prefix inserts the SAME zero-length target necklace. -/
def rightUnitNecklace (T : Object K x y q) :
    T.necklace ⟶ (concat T (unit K q y)).necklace where
  operator := prefixOperator T.necklace.dimension 0
  source := rfl
  target := Fin.ext rfl
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact (prefix_mem_concat_iff T.necklace Point.data s).mpr hs

/-- The SAME original zero-sided native map is literally the complete prefix inclusion. -/
theorem rightUnitNecklace_map (T : Object K x y q) :
    (rightUnitNecklace T).map.{u} = concatLeft T.necklace (unit K q y).necklace := by
  apply (cancel_mono (complex (concat T (unit K q y)).necklace.joints).ι).1
  rw [Morphism.map_ι, concatLeft_ι]
  rfl

/-- Every whole original flag is retained by the SAME native right-unit map. -/
theorem rightUnitNecklace_flags (T : Object K x y q) :
    (OriginalBead.OuterOperator.map (rightUnitNecklace T).operator
      (rightUnitNecklace T).source (rightUnitNecklace T).target).app q T.coefficient =
        (concat T (unit K q y)).coefficient := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    change ConcatFlags.prefixLift T.necklace.dimension 0 '' (T.coefficient.obj t).I =
      ConcatFlags.prefixLift T.necklace.dimension 0 '' (T.coefficient.obj t).I ∪
        ConcatFlags.suffixLift T.necklace.dimension 0 '' ((Point.pointCoefficient q).obj t).I
    ext i
    constructor
    · exact Or.inl
    · rintro (hi | hi)
      · exact hi
      · obtain ⟨j, _hj, rfl⟩ := hi
        have hj : j = ULift.up.{u} (0 : Fin 1) := @Subsingleton.elim (ULift.{u} (Fin 1)) inferInstance j _
        subst j
        exact ⟨ULift.up.{u} (Fin.last T.necklace.dimension), (T.coefficient.obj t).right,
          ULift.ext (Fin.ext rfl)⟩
  · intro i j f
    exact Subsingleton.elim _ _

/-- The actual full flagged map inserting the SAME original target unit. -/
def rightUnitMap (T : Object K x y q) : T ⟶ concat T (unit K q y) where
  necklaceMap := rightUnitNecklace T
  over := by
    rw [rightUnitNecklace_map]
    exact concat_first_input T (unit K q y)
  flags := rightUnitNecklace_flags T

namespace Components

/-- The SAME genuine source-zero necklace is the actual left unit on original component labels. -/
theorem concatenate_unit_left (a : ConnectedComponents (Object K x y q)) :
    concatenate (ConnectedComponents.mk (unit K q x)) a = a := by
  induction a using _root_.Quotient.inductionOn' with
  | h T => exact (_root_.Quotient.sound (Zigzag.of_hom (leftUnitMap T))).symm

/-- The SAME genuine target-zero necklace is the actual right unit on original component labels. -/
theorem concatenate_unit_right (a : ConnectedComponents (Object K x y q)) :
    concatenate a (ConnectedComponents.mk (unit K q y)) = a := by
  induction a using _root_.Quotient.inductionOn' with
  | h T => exact (_root_.Quotient.sound (Zigzag.of_hom (rightUnitMap T))).symm

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
