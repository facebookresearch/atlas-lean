/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceAssociatorReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentConcatenation

/-!
# Actual original flagged and component associativity

The full native three-piece associator retains each original input and
every original coefficient flag. The resulting actual flagged map
proves associativity of the SAME original component concatenation, with
arbitrary scalar degree and all four original vertex labels retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open SSet.OriginalNecklace

private instance {n : ℕ} (a b : SimplicialThickening.Path
    (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

variable {K : SSet.{u}} {w x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME original native associator retains the whole three-piece input. -/
theorem associator_over (T : Object K w x q) (U : Object K x y q) (V : Object K y z q) :
    (associatorMorphism T.necklace U.necklace V.necklace).map.{u} ≫
      (concat T (concat U V)).input = (concat (concat T U) V).input := by
  apply (concat_isPushout (T.necklace.concat U.necklace) V.necklace).hom_ext
  · apply (concat_isPushout T.necklace U.necklace).hom_ext
    · have h := congrArg (fun e => e ≫ (concat T (concat U V)).input)
        (associator_first.{u} T.necklace U.necklace V.necklace)
      simp only [Category.assoc] at h
      rw [h]
      change concatLeft T.necklace (U.necklace.concat V.necklace) ≫
        (concat T (concat U V)).input = concatLeft T.necklace U.necklace ≫
          concatLeft (T.necklace.concat U.necklace) V.necklace ≫ (concat (concat T U) V).input
      rw [concatLeft_input, concatLeft_input, concatLeft_input]
    · have h := congrArg (fun e => e ≫ (concat T (concat U V)).input)
        (associator_middle.{u} T.necklace U.necklace V.necklace)
      simp only [Category.assoc] at h
      rw [h]
      change concatLeft U.necklace V.necklace ≫ concatRight T.necklace (U.necklace.concat V.necklace) ≫
        (concat T (concat U V)).input = concatRight T.necklace U.necklace ≫
          concatLeft (T.necklace.concat U.necklace) V.necklace ≫ (concat (concat T U) V).input
      rw [concatRight_input, concatLeft_input, concatLeft_input, concatRight_input]
  · have h := congrArg (fun e => e ≫ (concat T (concat U V)).input)
      (associator_last.{u} T.necklace U.necklace V.necklace)
    simp only [Category.assoc] at h
    rw [h]
    change concatRight U.necklace V.necklace ≫ concatRight T.necklace (U.necklace.concat V.necklace) ≫
      (concat T (concat U V)).input =
        concatRight (T.necklace.concat U.necklace) V.necklace ≫ (concat (concat T U) V).input
    rw [concatRight_input, concatRight_input, concatRight_input]

/-- EVERY SAME full original flag follows the actual three-piece native associator. -/
theorem associator_flags (T : Object K w x q) (U : Object K x y q) (V : Object K y z q) :
    (OriginalBead.OuterOperator.map (associatorMorphism T.necklace U.necklace V.necklace).operator
      (associatorMorphism T.necklace U.necklace V.necklace).source
      (associatorMorphism T.necklace U.necklace V.necklace).target).app q
      (concat (concat T U) V).coefficient = (concat T (concat U V)).coefficient := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    let α := (associatorMorphism T.necklace U.necklace V.necklace).operator.toOrderHom.uliftMap
    have hT : α '' (ConcatFlags.prefixLift (T.necklace.dimension + U.necklace.dimension)
        V.necklace.dimension '' (ConcatFlags.prefixLift T.necklace.dimension U.necklace.dimension ''
          (T.coefficient.obj t).I)) =
        ConcatFlags.prefixLift T.necklace.dimension (U.necklace.dimension + V.necklace.dimension) ''
          (T.coefficient.obj t).I := by
      rw [Set.image_image, Set.image_image]
      congr 1
    have hU : α '' (ConcatFlags.prefixLift (T.necklace.dimension + U.necklace.dimension)
        V.necklace.dimension '' (ConcatFlags.suffixLift T.necklace.dimension U.necklace.dimension ''
          (U.coefficient.obj t).I)) =
        ConcatFlags.suffixLift T.necklace.dimension (U.necklace.dimension + V.necklace.dimension) ''
          (ConcatFlags.prefixLift U.necklace.dimension V.necklace.dimension '' (U.coefficient.obj t).I) := by
      rw [Set.image_image, Set.image_image, Set.image_image]
      congr 1
    have hV : α '' (ConcatFlags.suffixLift (T.necklace.dimension + U.necklace.dimension)
        V.necklace.dimension '' (V.coefficient.obj t).I) =
        ConcatFlags.suffixLift T.necklace.dimension (U.necklace.dimension + V.necklace.dimension) ''
          (ConcatFlags.suffixLift U.necklace.dimension V.necklace.dimension '' (V.coefficient.obj t).I) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext i
      apply ULift.ext
      apply Fin.ext
      change T.necklace.dimension + U.necklace.dimension + i.down.val =
        T.necklace.dimension + (U.necklace.dimension + i.down.val)
      omega
    change α '' (ConcatFlags.prefixLift (T.necklace.dimension + U.necklace.dimension) V.necklace.dimension ''
        (ConcatFlags.prefixLift T.necklace.dimension U.necklace.dimension '' (T.coefficient.obj t).I ∪
          ConcatFlags.suffixLift T.necklace.dimension U.necklace.dimension '' (U.coefficient.obj t).I) ∪
        ConcatFlags.suffixLift (T.necklace.dimension + U.necklace.dimension) V.necklace.dimension ''
          (V.coefficient.obj t).I) =
      ConcatFlags.prefixLift T.necklace.dimension (U.necklace.dimension + V.necklace.dimension) ''
          (T.coefficient.obj t).I ∪
        ConcatFlags.suffixLift T.necklace.dimension (U.necklace.dimension + V.necklace.dimension) ''
          (ConcatFlags.prefixLift U.necklace.dimension V.necklace.dimension '' (U.coefficient.obj t).I ∪
            ConcatFlags.suffixLift U.necklace.dimension V.necklace.dimension '' (V.coefficient.obj t).I)
    rw [Set.image_union, Set.image_union, Set.image_union, hT, hU, hV, Set.image_union, Set.union_assoc]
  · intro i j f
    exact Subsingleton.elim _ _

/-- The actual original full flagged associator, with all input and flag data retained. -/
def associatorMap (T : Object K w x q) (U : Object K x y q) (V : Object K y z q) :
    concat (concat T U) V ⟶ concat T (concat U V) where
  necklaceMap := associatorMorphism T.necklace U.necklace V.necklace
  over := associator_over T U V
  flags := associator_flags T U V

namespace Components

/-- Actual original component concatenation is associative at EVERY scalar and original label. -/
theorem concatenate_assoc (a : ConnectedComponents (Object K w x q))
    (b : ConnectedComponents (Object K x y q)) (c : ConnectedComponents (Object K y z q)) :
    concatenate (concatenate a b) c = concatenate a (concatenate b c) := by
  induction a using _root_.Quotient.inductionOn' with
  | h T =>
    induction b using _root_.Quotient.inductionOn' with
    | h U =>
      induction c using _root_.Quotient.inductionOn' with
      | h V => exact _root_.Quotient.sound (Zigzag.of_hom (associatorMap T U V))

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
