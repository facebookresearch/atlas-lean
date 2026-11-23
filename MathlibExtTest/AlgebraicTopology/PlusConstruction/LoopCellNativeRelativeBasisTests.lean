/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellNativeRelativeBasis

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology Topology.CWComplex
open AlgebraicTopology.LoopCellNativeRelativeBasis
open scoped Simplicial

universe u

attribute [local instance] TopCat.toSSet_obj_kanComplex

#check @nativeCoefficientBasisIso_deck
#print axioms nativeCoefficientBasisIso_deck
#check @nativeLambdaBasisIso
#print axioms nativeLambdaBasisIso
#check @originalRegularNativeChainIso_projection
#print axioms originalRegularNativeChainIso_projection
#check @originalRegularNativeHomologyIso_deck
#print axioms originalRegularNativeHomologyIso_deck
#check @originalRegularLambdaBasisIso
#print axioms originalRegularLambdaBasisIso
#check @originalQuotientDeckIndex_eq_canonical
#print axioms originalQuotientDeckIndex_eq_canonical
#check @actualThreeRelativeBoundaryIso
#print axioms actualThreeRelativeBoundaryIso
#check @upstairsThreeLambdaBasisIso_single
#print axioms upstairsThreeLambdaBasisIso_single
#check @actualOriginalRegularThreeToTwoMatrix_eq_id
#print axioms actualOriginalRegularThreeToTwoMatrix_eq_id
#check @actualThreeToTwoBoundary_eq
#print axioms actualThreeToTwoBoundary_eq

/-- The whole original regular quotient uses the original inclusion, actual
coefficient comparison, unchanged scalar-forgetful functor and native quotient. -/
theorem client_original_regular_quotient (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
        (TopCat.originalRegularRelativeChainProjection (LoopCellAttachment.inclusion X x P)
          (LoopCellAttachment.inclusion X x P x)) ≫
      (originalRegularNativeChainIso X x P).hom =
        (originalRegularNativeAmbientChainIso X x P).hom ≫
          (LoopCellPulledSimplicialModel.nativePair X x P).chainComplexπ
            (singularIntegralCoefficients : AddCommGrpCat.{u}) :=
  originalRegularNativeChainIso_projection X x P

/-- Every coefficient object and every quotient/cell label has the actual
LEFT geometric deck law on the entire relative summand. -/
theorem client_native_all_coefficient_deck (X : TopCat.{u}) [PathConnectedSpace X]
    [T2Space X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u})
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (q*r,p) ≫
        (nativeCoefficientBasisIso X x P R).hom =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P => R) (r,p) ≫
        (nativeCoefficientBasisIso X x P R).hom) ≫
          (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map
            (LoopCellQuotientCellPresentation.nativeDeckPair X x P q) :=
  nativeCoefficientBasisIso_deck X x P R q r p

/-- The ENTIRE original regular relative H2 group has a computed quotient-ring
basis with all actual closed-disk coefficients and its noncommutative deck law.
No expected basis or regular comparison is an input to this client. -/
theorem client_full_original_regular_basis (X : TopCat.{u}) [PathConnectedSpace X]
    [T2Space X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := originalRegularDeckModule X x P
    ∃ e : (P →₀ MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)) ≃ₗ[
        MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)] originalRegularHomologyTwo X x P,
      (∀ (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ),
        e (Finsupp.single p (MonoidAlgebra.single q z)) =
          (originalRegularNativeHomologyIso X x P).inv
            (((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
                (relativeSingularHomologyFunctor AddCommGrpCat.{u}
                  (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
                    (LoopCellQuotientCellPresentation.cellPairToCover X x P (q,p)))
                      (ULift.up z))) ∧
      ∀ (q : FundamentalGroup X x ⧸ P) (v : P →₀ MonoidAlgebra ℤ (FundamentalGroup X x ⧸ P)),
        originalRegularDeckRepresentation X x P q (e v) =
          e ((MonoidAlgebra.single q (1 : ℤ)) • v) := by
  let := originalRegularDeckModule X x P
  refine ⟨originalRegularLambdaBasisIso X x P, ?_, ?_⟩
  · exact fun q p z => originalRegularLambdaBasisIso_single X x P q p z
  · exact fun q v => originalRegularLambdaBasisIso_deck X x P q v

/-- The inverse recovers the literal quotient label and integer coefficient
from the same actual original two-disk relative class. -/
theorem client_original_regular_basis_inverse (X : TopCat.{u}) [PathConnectedSpace X]
    [T2Space X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    (originalRegularLambdaBasisIso X x P).symm
      ((originalRegularNativeHomologyIso X x P).inv
        (((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
            (relativeSingularHomologyFunctor AddCommGrpCat.{u}
              (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
                (LoopCellQuotientCellPresentation.cellPairToCover X x P (q,p))) (ULift.up z))) =
      Finsupp.single p (MonoidAlgebra.single q z) :=
  originalRegularLambdaBasisIso_inverse_single X x P q p z

/-- The original coefficient action uses the canonical quotient loop with
LEFT inverse precomposition and RIGHT inverse forward transport. -/
theorem client_original_two_action_conventions (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P)
    (γ : _root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x) ⟶
      _root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))
    (t : (CategoryTheory.regularPathModuleCoefficientFunctor
      (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))).obj
        (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))) :
    (TopCat.originalRegularDeckCoefficient (LoopCellAttachment.space X x P)
        (LoopCellAttachment.inclusion X x P x) (originalQuotientDeckIndex X x P q)).app
      (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x)) (FreeAbelianGroup.of γ) =
        FreeAbelianGroup.of
          (((LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q)⁻¹).asHom ≫ γ) ∧
    (LoopCellAttachment.regularQuotientGroupRingIso X x P).hom
        ((CategoryTheory.regularPathModuleCoefficientFunctor
          (_root_.FundamentalGroupoid.mk (LoopCellAttachment.inclusion X x P x))).map
            (FundamentalGroup.toArrow (LoopCellAttachment.fundamentalGroupQuotientMulEquiv X x P q)) t) =
      (LoopCellAttachment.regularQuotientGroupRingIso X x P).hom t *
        MonoidAlgebra.single q⁻¹ (1 : ℤ) :=
  ⟨originalRegularCoefficient_left_formula X x P q γ,
    originalRegularCoefficient_right_inverse X x P q t⟩

/-- The same actual three-cell boundary has the whole calibrated sphere
column before it is compared with the two-cell basis. -/
theorem client_actual_three_boundary_column (X : TopCat.{u}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (i : LoopCellQuotientCellPresentation.labels X x P) :
    (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) i ≫
      (upstairsThreeCoefficientIso X x P).hom) ≫ actualThreeRelativeBoundary X x P =
        classicalCellBoundaryHomologyTwoGenerator.{u} ≫
          (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{u})).map
              (chosenSphericalCopy X x P i)) ≫
                LoopCellSphericalGenerators.relativeProjection X x P := by
  let j := Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
    (singularIntegralCoefficients : AddCommGrpCat.{u})) i
  exact (Category.assoc j (upstairsThreeCoefficientIso X x P).hom
      (actualThreeRelativeBoundary X x P)).trans
    ((congrArg (fun f => j ≫ f) (actualThreeToTwoBoundary_eq X x P).symm).trans
      (actualThreeToTwoBoundary_ι X x P i))

/-- The entire integer coefficient of every actual three-cell class, and its
inverse coordinate, use the SAME sphere attachment and literal quotient label. -/
theorem client_actual_three_cell_basis_and_inverse (X : TopCat.{u}) [PathConnectedSpace X]
    [T2Space X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (q : FundamentalGroup X x ⧸ P) (p : P) (z : ℤ) :
    upstairsThreeLambdaBasisIso X x P (Finsupp.single p (MonoidAlgebra.single q z)) =
      (Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z) ∧
    (upstairsThreeLambdaBasisIso X x P).symm
      ((Sigma.ι (fun _ : LoopCellQuotientCellPresentation.labels X x P =>
        (singularIntegralCoefficients : AddCommGrpCat.{u})) (q,p) ≫
          (upstairsThreeCoefficientIso X x P).hom) (ULift.up z)) =
      Finsupp.single p (MonoidAlgebra.single q z) :=
  ⟨upstairsThreeLambdaBasisIso_single X x P q p z,
    upstairsThreeLambdaBasisIso_inverse_single X x P q p z⟩

/-- The whole geometric upstairs boundary has identity quotient-ring matrix
in the ORIGINAL regular H2 basis, and its value is the actual LES map followed
by the proven original inverse comparison. This makes no claim that the
upstairs projection is already a covering of the downstairs three-cell space. -/
theorem client_entire_original_target_matrix (X : TopCat.{u}) [PathConnectedSpace X]
    [T2Space X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    actualOriginalRegularThreeToTwoMatrix X x P = LinearMap.id ∧
    ∀ a : upstairsThreeHomology X x P,
      actualThreeToOriginalRegularLambdaMap X x P a =
        (originalRegularNativeHomologyIso X x P).inv (actualThreeRelativeBoundary X x P a) :=
  ⟨actualOriginalRegularThreeToTwoMatrix_eq_id X x P,
    fun a => actualThreeToOriginalRegularLambdaMap_apply X x P a⟩

end
