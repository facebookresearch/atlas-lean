/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanDiagonalTotalNaturality

/-!
# Naturality on the actual BK carrier homology

The genuine carrier-chain isomorphism transports the original diagonal/total
homology square to the actual carrier. Both sides retain their original maps
and directions.
-/

public section

noncomputable section

open CategoryTheory Limits

universe uJ vJ

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKHomologyTests

variable {J : Type uJ} [Category.{vJ} J]

/-- Applying homology to the actual carrier presentation transports the
original square in its stated direction, retaining the original total map. -/
theorem originalCarrierHomology_naturality
    (R : AddCommGrpCat.{max uJ vJ}) {D E : J ⥤ SSet.{max uJ vJ}}
    (α : D ⟶ E) (n : ℕ) :
    let c := fun F : J ⥤ SSet.{max uJ vJ} =>
      SSet.bkCarrierChainIso AddCommGrpCat.{max uJ vJ} R F
    let h := fun F : J ⥤ SSet.{max uJ vJ} =>
      HomologicalComplex.homologyMapIso (c F) n ≪≫ SSet.bkDiagonalTotalHomologyIso R F n
    SSet.homologyMap (SSet.bkHocolimMap α) R n ≫ (h E).hom =
      (h D).hom ≫ HomologicalComplex.homologyMap
        ((SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{max uJ vJ} R).map α) n := by
  let cD := SSet.bkCarrierChainIso AddCommGrpCat.{max uJ vJ} R D
  let cE := SSet.bkCarrierChainIso AddCommGrpCat.{max uJ vJ} R E
  let f := SSet.chainComplexMap (SSet.bkHocolimMap α) R
  let a := (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{max uJ vJ}).map
    ((SSet.coproductLinearizationFunctor AddCommGrpCat.{max uJ vJ} R).map (SSet.bkHocolimMap α))
  let t := (SSet.bkAlternatingTotalComplexFunctor AddCommGrpCat.{max uJ vJ} R).map α
  have hc : f ≫ cE.hom = cD.hom ≫ a :=
    SSet.bkCarrierChainIso_naturality AddCommGrpCat.{max uJ vJ} R α
  have hcH := HomologicalComplex.homologyMap_square hc n
  have heH := SSet.bkDiagonalTotalHomologyIso_naturality R α n
  change HomologicalComplex.homologyMap f n ≫
      (HomologicalComplex.homologyMap cE.hom n ≫ (SSet.bkDiagonalTotalHomologyIso R E n).hom) =
    (HomologicalComplex.homologyMap cD.hom n ≫ (SSet.bkDiagonalTotalHomologyIso R D n).hom) ≫
      HomologicalComplex.homologyMap t n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (SSet.bkDiagonalTotalHomologyIso R E n).hom) hcH).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => HomologicalComplex.homologyMap cD.hom n ≫ g) heH).trans
          (Category.assoc _ _ _).symm)))

end MathlibExtTest.AlgebraicTopology.SimplicialSet.CommonUniverseBKHomologyTests

end
