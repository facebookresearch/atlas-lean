/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellQuotientCellPresentation

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open AlgebraicTopology.LoopCellQuotientCellPresentation

universe u

#check AlgebraicTopology.LoopCellQuotientCellPresentation.classicalIsPushout
#print axioms AlgebraicTopology.LoopCellQuotientCellPresentation.classicalIsPushout
#check AlgebraicTopology.LoopCellQuotientCellPresentation.classicalSpaceIso
#print axioms AlgebraicTopology.LoopCellQuotientCellPresentation.classicalSpaceIso
#check AlgebraicTopology.LoopCellQuotientCellPresentation.relativeCoefficientBasisIso
#print axioms AlgebraicTopology.LoopCellQuotientCellPresentation.relativeCoefficientBasisIso
#check AlgebraicTopology.LoopCellQuotientCellPresentation.cellPairToCover_unit
#print axioms AlgebraicTopology.LoopCellQuotientCellPresentation.cellPairToCover_unit
#check AlgebraicTopology.LoopCellQuotientCellPresentation.cellPairToCover_deck
#print axioms AlgebraicTopology.LoopCellQuotientCellPresentation.cellPairToCover_deck

/-- Every actual labelled disk retains its whole native lift and its actual original label. -/
theorem client_whole_labelled_disk (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (q : FundamentalGroup X x ⧸ P) (p : P) :
    TopPair.Hom.fst (cellPairToCover X x P (q,p)) =
      (LoopCellSphericalGenerators.diskBoundaryArrowIso.{u} 2).inv.right ≫
        SSet.toTop.map (LoopCellSphericalGenerators.nativeDiskLift X x P p ≫ nativeDeck X x P q) :=
  cellPairToCover_fst X x P (q,p)

/-- The genuine inverse returns every actual whole disk-pair class to its exact (q,p) coordinate. -/
theorem client_entire_cell_basis_inverse (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (R : AddCommGrpCat.{u})
    (q : FundamentalGroup X x ⧸ P) (p : P) :
    ((Topology.CWComplex.classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u,u}
        R 2).hom ≫
      (relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2).map (cellPair X x P (q,p))) ≫
        (relativeCoefficientBasisIso X x P R).inv =
      Sigma.ι (fun _ : labels X x P => R) (q,p) :=
  relativeCoefficientBasisIso_inverse_ι X x P R (q,p)

/-- The unit label is the SAME original chosen lifted pair, including its first-path shift. -/
theorem client_original_unit_pair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] (p : P) :
    cellPairToCover X x P (1,p) = LoopCellSphericalGenerators.liftedCharacteristicDiskPair X x P p :=
  cellPairToCover_unit X x P p

/-- Literal noncommutative LEFT multiplication acts on the SAME entire original characteristic pair. -/
theorem client_noncommutative_pair_deck (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (q r : FundamentalGroup X x ⧸ P) (p : P) :
    cellPairToCover X x P (q*r,p) = cellPairToCover X x P (r,p) ≫ nativeDeckPair X x P q :=
  cellPairToCover_deck X x P q r p

end
