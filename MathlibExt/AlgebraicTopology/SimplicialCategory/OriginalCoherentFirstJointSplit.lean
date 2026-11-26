/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentGeneratorInterval
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagSupport
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCompositionLaws

/-!
# Splitting the same original complete first-joint coefficient

A vertex in the original first flag belongs to every original flag.
The native composition-face inverse gives both entire original interval
coefficients. Their same original union recovers the whole original
coefficient, including either endpoint as the supplied joint.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.FirstJoint

open SimplicialEnrichment
open TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The entire same original bead coefficient with its actual native path-nerve type. -/
def originalCoefficient (b : Bead K x y q) : (coefficientObject.{u} b.dimension).obj q :=
  b.coefficient

/-- The original individual input vertex at the supplied original first-flag joint. -/
def middle (b : Bead K x y q) (j : Fin (b.dimension + 1)) : K _⦋0⦌ :=
  vertex K b.simplex (.mk (ULift.up.{u} j))

/-- The actual original full composition-face coefficient at this joint. -/
def positive (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (CompositionFace.positive (ULift.up.{u} (0 : Fin (b.dimension + 1)))
      (ULift.up.{u} j) (ULift.up.{u} (Fin.last b.dimension)) : SSet.{u}).obj q :=
  ⟨originalCoefficient b, fun t =>
    ((originalCoefficient b).map (homOfLE (Fin.zero_le t))).hom.down.down hj⟩

/-- The whole original left interval coefficient, from the native composition-face inverse. -/
def leftCoefficient (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (nerve (SimplicialThickening.Path
      (ULift.up.{u} (0 : Fin (b.dimension + 1))) (ULift.up.{u} j))).obj q :=
  CompositionFace.leftChain _ _ _ (positive b j hj)

/-- The whole original right interval coefficient, from the same native inverse. -/
def rightCoefficient (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (nerve (SimplicialThickening.Path
      (ULift.up.{u} j) (ULift.up.{u} (Fin.last b.dimension)))).obj q :=
  CompositionFace.rightChain _ _ _ (positive b j hj)

/-- Every left flag is its same entire original interval intersection. -/
theorem left_flags (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I)
    (t : Fin (q.unop.len + 1)) :
    ((leftCoefficient b j hj).obj t).I =
      ((originalCoefficient b).obj t).I ∩ Set.Iic (ULift.up.{u} j) := rfl

/-- Every right flag is its same entire original interval intersection. -/
theorem right_flags (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I)
    (t : Fin (q.unop.len + 1)) :
    ((rightCoefficient b j hj).obj t).I =
      ((originalCoefficient b).obj t).I ∩ Set.Ici (ULift.up.{u} j) := rfl

/-- The same original whole coherent composition map at the supplied first-flag joint. -/
def compositionMap (b : Bead K x y q) (j : Fin (b.dimension + 1)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (b.dimension + 1)))
      (ULift.up.{u} j)) ⊗
        nerve (SimplicialThickening.Path (ULift.up.{u} j) (ULift.up.{u} (Fin.last b.dimension))) ⟶
          coefficientObject.{u} b.dimension :=
  CompositionFace.composition _ _ _

private instance {J : Type u} [LinearOrder J] (i k : J)
    (a b : SimplicialThickening.Path i k) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Gluing both complete actual interval coefficients recovers the same entire original coefficient. -/
theorem coefficient_union (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    (compositionMap b j).app q (leftCoefficient b j hj, rightCoefficient b j hj) =
      originalCoefficient b := by
  refine Functor.ext (fun t => ?_) ?_
  · exact CompositionFace.union_split ((originalCoefficient b).obj t) ((positive b j hj).property t)
  · intro i k f
    exact Subsingleton.elim _ _

/-- The complete original left generator at the same supplied input simplex and original labels. -/
def leftArrow (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    Arrow K x (middle b j) q :=
  ⟨⦋b.dimension⦌, b.simplex, initial.{u} b.dimension, .mk (ULift.up.{u} j),
    b.source_eq, rfl, leftCoefficient b j hj⟩

/-- The complete original right generator at the same whole input simplex and labels. -/
def rightArrow (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    Arrow K (middle b j) y q :=
  ⟨⦋b.dimension⦌, b.simplex, .mk (ULift.up.{u} j), terminal.{u} b.dimension,
    rfl, b.target_eq, rightCoefficient b j hj⟩

/-- The entire actual left original endpoint bead. -/
def leftBead (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    Bead K x (middle b j) q := trim (leftArrow b j hj)

/-- The entire actual right original endpoint bead. -/
def rightBead (b : Bead K x y q) (j : Fin (b.dimension + 1))
    (hj : ULift.up.{u} j ∈ ((originalCoefficient b).obj 0).I) :
    Bead K (middle b j) y q := trim (rightArrow b j hj)

end CategoryTheory.CoherentRealization.OriginalBead.FirstJoint
