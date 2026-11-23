/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellPerfectHomology

/-! Direct original-map, calibrated-loop, connecting-map and generator clients. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u v

#check @Abelianization.map_bijective_of_surjective_of_isPerfect_ker
#print axioms Abelianization.map_bijective_of_surjective_of_isPerfect_ker
#check @TopCat.fundamentalGroupAbelianizationHomologyOneIso
#print axioms TopCat.fundamentalGroupAbelianizationHomologyOneIso
#check @TopCat.fundamentalGroupHomologyOneHom_fromPath
#print axioms TopCat.fundamentalGroupHomologyOneHom_fromPath
#check @TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality
#print axioms TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality
#check @LoopCellAttachment.inclusionHomologyOne_isIso_of_perfect
#print axioms AlgebraicTopology.LoopCellAttachment.inclusionHomologyOne_isIso_of_perfect
#check @LoopCellAttachment.relativeBoundaryHomologyTwoInt_eq_zero_of_perfect
#print axioms AlgebraicTopology.LoopCellAttachment.relativeBoundaryHomologyTwoInt_eq_zero_of_perfect
#check @LoopCellAttachment.absoluteToRelativeHomologyTwo_epi_of_perfect
#print axioms AlgebraicTopology.LoopCellAttachment.absoluteToRelativeHomologyTwo_epi_of_perfect
#check @LoopCellAttachment.exists_absoluteHomologyTwo_generator_lift_of_perfect
#print axioms AlgebraicTopology.LoopCellAttachment.exists_absoluteHomologyTwo_generator_lift_of_perfect

-- The derived inverse preserves the original f-image, with independent group universes.
example {G : Type u} [Group G] {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsPerfect f.ker] (g : G) :
    (MulEquiv.ofBijective (Abelianization.map f)
      (Abelianization.map_bijective_of_surjective_of_isPerfect_ker f hf)).symm
        (Abelianization.of (f g)) = Abelianization.of g := by
  let e := MulEquiv.ofBijective (Abelianization.map f)
    (Abelianization.map_bijective_of_surjective_of_isPerfect_ker f hf)
  change e.symm (e (Abelianization.of g)) = Abelianization.of g
  exact e.symm_apply_apply _

-- The first Hurewicz Iso maps the actual loop to its literal positive singular edge cycle.
example (X : TopCat.{u}) [PathConnectedSpace X] (x : X) (γ : _root_.Path x x) :
    let K := TopCat.toSSet.obj X
    let R := (singularIntegralCoefficients : AddCommGrpCat.{u})
    let e : K.Edge (TopCat.toSSetObj₀Equiv.symm x)
        (TopCat.toSSetObj₀Equiv.symm x) :=
      (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).symm
        ((TopCat.pathEquiv (X := X) (x := x) (y := x)).symm γ)
    (TopCat.fundamentalGroupAbelianizationHomologyOneIso X x).hom
      (Additive.ofMul (Abelianization.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
      (((K.chainComplex R).liftCycles (K.ιChainComplex (R := R) e.edge) 0 (by simp)
        (by
          rw [SSet.ιChainComplex_d, Fin.sum_univ_two]
          simp [e.tgt_eq, e.src_eq]) ≫ (K.chainComplex R).homologyπ 1)
            (ULift.up (1 : ℤ))) := by
  dsimp only
  rw [TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_of,
    TopCat.fundamentalGroupHomologyOneHom_fromPath]
  exact congrArg
    (fun f : (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) => f (ULift.up (1 : ℤ)))
    (TopCat.pathHomologyOneClass_eq_singularCycle X x γ)

-- The original topological map supplies the actual homology-map square.
example {X Y : TopCat.{u}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (x : X) :
    AddCommGrpCat.ofHom
      ((Abelianization.map (FundamentalGroup.mapOfEq f.hom rfl)).toAdditive) ≫
        (TopCat.fundamentalGroupAbelianizationHomologyOneIso Y (f x)).hom =
      (TopCat.fundamentalGroupAbelianizationHomologyOneIso X x).hom ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map f) :=
  TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality f x

variable (X : TopCat.{u}) [hX : PathConnectedSpace X] (x : X)
variable (P : Subgroup (FundamentalGroup X x)) [hP : P.Normal] [hperfect : Group.IsPerfect P]

include hX hP hperfect

-- The actual old-space inclusion, not an assumed H1 comparison, is an isomorphism.
example : IsIso (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u})).map
      (LoopCellAttachment.inclusion X x P)) :=
  LoopCellAttachment.inclusionHomologyOne_isIso_of_perfect X x P

-- The actual full relative boundary is zero in the original pair.
example : (singularHomologyIntData AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u})).boundary 2
      (LoopCellAttachment.relativePair X x P) = 0 :=
  LoopCellAttachment.relativeBoundaryHomologyTwoInt_eq_zero_of_perfect X x P

-- Every original indexed characteristic generator is preserved in this equality.
example (p : P) :
    LoopCellAttachment.relativeGenerator X x P
      (singularIntegralCoefficients : AddCommGrpCat.{u}) p ≫
        LoopCellAttachment.relativeBoundaryHomologyTwo X x P = 0 :=
  LoopCellAttachment.relativeGenerator_boundary_eq_zero_of_perfect X x P p

-- The actual relative-chain quotient is epic in degree two.
example : Epi (LoopCellAttachment.absoluteToRelativeHomologyTwo X x P) :=
  LoopCellAttachment.absoluteToRelativeHomologyTwo_epi_of_perfect X x P

-- Every relative class has an absolute preimage; no desired relative Iso is supplied.
example (z : (relativeSingularHomologyFunctor AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).obj
      (LoopCellAttachment.relativePair X x P)) :
    ∃ a : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
          (LoopCellAttachment.space X x P)),
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P a = z :=
  LoopCellAttachment.absoluteToRelativeHomologyTwo_surjective_of_perfect X x P z

-- In particular the original pth two-cell class has an absolute lift.
example (p : P) :
    ∃ a : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
          (LoopCellAttachment.space X x P)),
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P a =
        LoopCellAttachment.relativeGenerator X x P
          (singularIntegralCoefficients : AddCommGrpCat.{u}) p (ULift.up (1 : ℤ)) :=
  LoopCellAttachment.exists_absoluteHomologyTwo_generator_lift_of_perfect X x P p

end
