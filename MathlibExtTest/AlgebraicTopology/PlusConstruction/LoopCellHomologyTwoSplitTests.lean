/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellHomologyTwoSplit

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

#check @AlgebraicTopology.LoopCellAttachment.homologyTwoShortComplex
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoShortComplex
#check @AlgebraicTopology.LoopCellAttachment.homologyTwoShortExact
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoShortExact
#check @AlgebraicTopology.LoopCellAttachment.homologyTwoSplitting
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSplitting

#check @LoopCellAttachment.homologyTwoSplitIso
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSplitIso
#check @LoopCellAttachment.homologyTwoProjection
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoProjection
#check @LoopCellAttachment.homologyTwoProjection_eq
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoProjection_eq
#check @LoopCellAttachment.homologyTwoSection
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSection
#check @LoopCellAttachment.homologyTwoSplitIso_inv
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSplitIso_inv
#check @LoopCellAttachment.homologyTwoSplitIso_inclusion
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSplitIso_inclusion
#check @LoopCellAttachment.homologyTwoSplitIso_projection
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoSplitIso_projection
#check @LoopCellAttachment.homologyTwoGeneratorLift_relative
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoGeneratorLift_relative
#check @LoopCellAttachment.homologyTwoGeneratorLift_coordinate
#print axioms AlgebraicTopology.LoopCellAttachment.homologyTwoGeneratorLift_coordinate

variable (X : TopCat.{u}) [hX : PathConnectedSpace X] (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [hP : P.Normal] [hp : Group.IsPerfect P]
include hX hP hp

-- The original H2 space, original H2 source and literal all-P free group are returned.
example :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) ≅
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) ⊞
            (∐ fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) :=
  LoopCellAttachment.homologyTwoSplitIso X x P

-- This is a computed strict section of the actual whole free-cell projection.
example : LoopCellAttachment.homologyTwoSection X x P ≫
    LoopCellAttachment.homologyTwoProjection X x P =
      𝟙 (LoopCellAttachment.homologyTwoCells X x P) :=
  LoopCellAttachment.homologyTwoSection_projection X x P

-- The FIRST coordinate is calibrated to the literal original inclusion map.
example : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u})).map
      (LoopCellAttachment.inclusion X x P)) ≫
        (LoopCellAttachment.homologyTwoSplitIso X x P).hom = biprod.inl :=
  LoopCellAttachment.homologyTwoSplitIso_inclusion X x P

-- The SECOND coordinate is the original relative chain map followed by its cell coordinate.
example : (LoopCellAttachment.homologyTwoSplitIso X x P).hom ≫ biprod.snd =
    LoopCellAttachment.absoluteToRelativeHomologyTwo X x P ≫
      (LoopCellAttachment.relativeHomologyTwoIso X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u})).inv := by
  calc
    _ = LoopCellAttachment.homologyTwoProjection X x P :=
      LoopCellAttachment.homologyTwoSplitIso_projection X x P
    _ = _ := LoopCellAttachment.homologyTwoProjection_eq X x P

-- The inverse contains the actual original inclusion, not an unspecified map of groups.
example : (LoopCellAttachment.homologyTwoSplitIso X x P).inv =
    biprod.desc
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map
          (LoopCellAttachment.inclusion X x P))
      (LoopCellAttachment.homologyTwoSection X x P) :=
  LoopCellAttachment.homologyTwoSplitIso_inv X x P

example : (LoopCellAttachment.homologyTwoSplitIso X x P).hom ≫
    (LoopCellAttachment.homologyTwoSplitIso X x P).inv = 𝟙 _ :=
  LoopCellAttachment.homologyTwoSplitIso_hom_inv X x P

example : (LoopCellAttachment.homologyTwoSplitIso X x P).inv ≫
    (LoopCellAttachment.homologyTwoSplitIso X x P).hom = 𝟙 _ :=
  LoopCellAttachment.homologyTwoSplitIso_inv_hom X x P

-- The complete chosen section recovers the original relative-H2 coordinate.
example : LoopCellAttachment.homologyTwoSection X x P ≫
    LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
      (LoopCellAttachment.relativeHomologyTwoIso X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u})).hom :=
  LoopCellAttachment.homologyTwoSection_relative X x P

-- EVERY indexed generator, including the identity element of P, keeps its whole relative map.
example (p : P) : LoopCellAttachment.homologyTwoGeneratorLift X x P p ≫
    LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p :=
  LoopCellAttachment.homologyTwoGeneratorLift_relative X x P p

-- Its actual direct-sum coordinate is (0,e_p), with the original ordering retained.
example (p : P) : LoopCellAttachment.homologyTwoGeneratorLift X x P p ≫
    (LoopCellAttachment.homologyTwoSplitIso X x P).hom =
      Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
        biprod.inr :=
  LoopCellAttachment.homologyTwoGeneratorLift_coordinate X x P p

-- The positive integral characteristic generator is the SAME original relative class.
example (p : P) : LoopCellAttachment.absoluteToRelativeHomologyTwo X x P
    (LoopCellAttachment.homologyTwoGeneratorLift X x P p (ULift.up (1 : ℤ))) =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p (ULift.up (1 : ℤ)) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      (LoopCellAttachment.homologyTwoGeneratorLift_relative X x P p) (ULift.up (1 : ℤ))

-- The two coordinates reconstruct EVERY original H2 class as a whole group map.
example : LoopCellAttachment.homologyTwoRetraction X x P ≫
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (LoopCellAttachment.inclusion X x P)) +
        LoopCellAttachment.homologyTwoProjection X x P ≫
          LoopCellAttachment.homologyTwoSection X x P = 𝟙 _ :=
  LoopCellAttachment.homologyTwo_decomposition X x P

end
