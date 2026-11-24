/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EqualCharacteristicFFRingModels
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Native equal-characteristic Frobenius sheaves and invariant structure

Every chart Frobenius is fixed by the actual coefficientwise q-power
map on R+[[t]]. Its sheaf map is normalized by the same actual rational
ring comparisons. On the original native point quotient, the structure
sheaf is the actual equalizer of Frobenius and identity on the pushed
annular sheaf. No alternate curve-ring or structure-sheaf carrier is used.

Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.2;
the native generic invariant-sheaf integration follows the completed
TauCeti source attributed in `IntegralFarguesFontaineModels`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EqualCharacteristicFFSheafModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.TopologicalSpace
open EqualCharacteristicCoefficientModels EqualCharacteristicFFRingModels

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Fintype k]
  (C : ResidueData p k) (S : Base p k C) [D : RationalRestrictions p k C S]
  (F : FrobeniusPoints p k C S)

/-- Actual coefficient-normalized rational-chart Frobenius output. -/
structure FrobeniusCharts where
  chart : RationalPresentation p k C S ⥤ RationalPresentation p k C S
  numerators : ∀ P, (chart.obj P).numerators =
    P.numerators.map ⟨frobenius p k C S, (frobenius p k C S).injective⟩
  denominator : ∀ P, (chart.obj P).denominator = frobenius p k C S P.denominator
  opens : ∀ P, (chart.obj P).openSet = (Opens.map (frobeniusMap p k C S F)).obj P.openSet
  map : ∀ P, ChartRing p k C S P →+* ChartRing p k C S (chart.obj P)
  coefficient : ∀ P, (map P).comp (chartCoefficient p k C S P) =
    (chartCoefficient p k C S (chart.obj P)).comp (frobenius p k C S).toRingHom
  continuous : ∀ P, Continuous (map P)
  naturality : ∀ {P Q : RationalPresentation p k C S} (h : Q.openSet ≤ P.openSet),
    (map Q).comp (D.restrict h) =
      (D.restrict (leOfHom (chart.map (show Q ⟶ P from homOfLE h)))).comp (map P)

variable (O : PeriodSheaf p k C S) (A : FrobeniusCharts p k C S F)

/-- The original sheaf Frobenius is fixed on every actual rational-chart section. -/
structure SheafFrobenius where
  map : O.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p k C S F)).obj O.sheaf
  normalized : ∀ P,
    map.hom.app (op P.openSet) ≫ O.sheaf.obj.map (eqToHom (A.opens P)).op ≫
      O.rationalComparison.hom.app (op (A.chart.obj P)) =
        O.rationalComparison.hom.app (op P) ≫ CommRingCat.ofHom (A.map P)

variable (G : SheafFrobenius p k C S F O A)

/-- The actual Frobenius endomorphism of the quotient-pushed original presheaf. -/
def pushedFrobenius :
    (TopCat.Presheaf.pushforward CommRingCat (quotient p k C S F)).obj O.sheaf.obj ⟶
      (TopCat.Presheaf.pushforward CommRingCat (quotient p k C S F)).obj O.sheaf.obj :=
  (TopCat.Presheaf.pushforward CommRingCat (quotient p k C S F)).map G.map.hom ≫
    eqToHom ((TopCat.Presheaf.Pushforward.comp_eq
      (frobeniusMap p k C S F) (quotient p k C S F) O.sheaf.obj).symm.trans
        (TopCat.Presheaf.pushforward_eq' (quotient_frobenius p k C S F) O.sheaf.obj))

/-- The same actual map regarded as a sheaf morphism. -/
def sheafFrobenius :
    (TopCat.Sheaf.pushforward CommRingCat (quotient p k C S F)).obj O.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat (quotient p k C S F)).obj O.sheaf :=
  ⟨pushedFrobenius p k C S F O A G⟩

/-- The structure sheaf is the actual invariant-sheaf equalizer. -/
def structureSheaf : TopCat.Sheaf CommRingCat (xSpace p k C S F) :=
  equalizer (sheafFrobenius p k C S F O A G) (𝟙 _)

/-- The original native inclusion of invariant sections into the pushed annular sheaf. -/
def invariantInclusion : structureSheaf p k C S F O A G ⟶
    (TopCat.Sheaf.pushforward CommRingCat (quotient p k C S F)).obj O.sheaf :=
  equalizer.ι (sheafFrobenius p k C S F O A G) (𝟙 _)

/-- Native equalizer sections satisfy the displayed actual Frobenius equation. -/
theorem invariant_frobenius :
    invariantInclusion p k C S F O A G ≫ sheafFrobenius p k C S F O A G =
      invariantInclusion p k C S F O A G := by
  dsimp only [invariantInclusion, structureSheaf]
  exact (equalizer.condition _ _).trans (Category.comp_id _)

end MathlibExt.AlgebraicGeometry.EqualCharacteristicFFSheafModels
