/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FarguesFontaineSheafModels

/-!
# Actual base and Frobenius-orbit maps for FF models

The map on integral period rings is the actual Witt map on the integral
plus subrings of a bounded geometric perfectoid morphism. A point-map
dictionary is fixed on every all-rank valuation by that ring map. Its
Frobenius-compatible orbit map is then constructed by the native
coequalizer universal property, with the projection equation proved.

These source dictionaries are the local geometric input; no free curve
map is selected and no generic adic-gluing result is requested again.
Reference: Fargues--Scholze, arXiv:2102.13459v4, SectionI.2.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.FarguesFontainePointFunctoriality

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open IntegralFarguesFontaineModels
open FarguesFontaineSheafModels

variable (p : ℕ) [Fact p.Prime]

/-- The normalized annular/source Frobenius model at an actual perfectoid base. -/
structure Source (S : Base p) where
  [restrictions : RationalRestrictions p S]
  phi : FrobeniusPoints p S
  period : PeriodSheaf p S
  chartFunctor : RationalPresentation p S ⥤ RationalPresentation p S
  chartMaps : FrobeniusMapFamily p S chartFunctor
  [chartLaws : IsFrobeniusCharts p S phi chartFunctor chartMaps]
  sheafMap : period.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p S phi)).obj period.sheaf
  [sheafLaw : IsSheafFrobenius p S phi period chartFunctor chartMaps sheafMap]

variable {p} {S T : Base p}

/-- The actual plus-subring map of a geometric perfectoid morphism. -/
def plusMap (f : S.pair ⟶ T.pair) : T.pair.plus →+* S.pair.plus where
  toFun a := ⟨f.hom a.val, f.plus a.val a.property⟩
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' a b := by ext; exact map_add _ _ _
  map_mul' a b := by ext; exact map_mul _ _ _

/-- The actual contravariant integral-Witt coefficient map. -/
def periodMap (f : S.pair ⟶ T.pair) : Ring p T →+* Ring p S :=
  WittVector.map (plusMap f)

variable (A : Source p S) (B : Source p T) (f : S.pair ⟶ T.pair)

/-- The source point map, fixed on all valuation relations and Frobenius. -/
structure PointMap where
  map : ySpace p S ⟶ ySpace p T
  normalized : ∀ y : Y p S,
    (map y).val.val = AffineAdicSpectra.comap (periodMap f) y.val.val
  frobenius : frobeniusMap p S A.phi ≫ map = map ≫ frobeniusMap p T B.phi

variable (F : PointMap A B f)

/-- The actual map of orbit spaces, descended from the specified Witt point map. -/
def orbitMap : xSpace p S A.phi ⟶ xSpace p T B.phi :=
  coequalizer.desc (F.map ≫ quotient p T B.phi) (by
    calc
      frobeniusMap p S A.phi ≫ (F.map ≫ quotient p T B.phi) =
          (frobeniusMap p S A.phi ≫ F.map) ≫ quotient p T B.phi :=
        (Category.assoc _ _ _).symm
      _ = (F.map ≫ frobeniusMap p T B.phi) ≫ quotient p T B.phi := by rw [F.frobenius]
      _ = F.map ≫ quotient p T B.phi := by
        rw [Category.assoc, quotient_frobenius]
      _ = 𝟙 (ySpace p S) ≫ (F.map ≫ quotient p T B.phi) := (Category.id_comp _).symm)

/-- The orbit map is fixed by the actual quotient-projection equation. -/
theorem quotient_orbitMap :
    quotient p S A.phi ≫ orbitMap A B f F = F.map ≫ quotient p T B.phi :=
  coequalizer.π_desc _ _

end MathlibExt.AlgebraicGeometry.FarguesFontainePointFunctoriality
