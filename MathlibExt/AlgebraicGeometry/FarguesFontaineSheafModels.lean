/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralFarguesFontaineModels
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Core

/-!
# Actual invariant structure sheaf and vector bundles on an FF model

Frobenius on rational charts is normalized to the actual Witt coefficient
map. Its sheaf map is pinned by those same chart comparisons. On the
native Frobenius point quotient the structure sheaf is the actual equalizer
of Frobenius and identity on q_*O_Y. Vector bundles are native locally free
finite-type modules on this sheaf, with their actual stalk rank and module
isomorphisms. There is no abstract bundle groupoid or curve-ring oracle.

The annular sheaf and Frobenius dictionaries are ordinary completed-source
integration inputs from TauCeti's FF quotient; no generic gluing theorem
is requested again. Relative functor, untilt divisor/completion and bundle
modification comparisons remain additional geometric contracts.

Reference: Fargues--Scholze, arXiv:2102.13459v4, SectionI.2;
TauCeti FF/PreAdicSpace.lean and Adic.lean at the revision cited in the
imported integral model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.FarguesFontaineSheafModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.TopologicalSpace
open IntegralFarguesFontaineModels

variable (p : ℕ) [Fact p.Prime] (S : Base p)
  [D : RationalRestrictions p S] (φ : FrobeniusPoints p S)

def FrobeniusNumerators (L : RationalPresentation p S ⥤ RationalPresentation p S) : Prop :=
  ∀ P, (L.obj P).numerators =
    P.numerators.map ⟨frobenius p S, (frobenius p S).injective⟩

def FrobeniusDenominator (L : RationalPresentation p S ⥤ RationalPresentation p S) : Prop :=
  ∀ P, (L.obj P).denominator = frobenius p S P.denominator

def FrobeniusOpens (L : RationalPresentation p S ⥤ RationalPresentation p S) : Prop :=
  ∀ P, (L.obj P).openSet = (Opens.map (frobeniusMap p S φ)).obj P.openSet

abbrev FrobeniusMapFamily (L : RationalPresentation p S ⥤ RationalPresentation p S) :=
  ∀ P : RationalPresentation p S, ChartRing p S P →+* ChartRing p S (L.obj P)

def FrobeniusMapNaturality (L : RationalPresentation p S ⥤ RationalPresentation p S)
    (m : FrobeniusMapFamily p S L) : Prop :=
  ∀ {P Q : RationalPresentation p S} (h : Q.openSet ≤ P.openSet),
    (m Q).comp (D.restrict h) =
      (D.restrict (leOfHom (L.map (show Q ⟶ P from homOfLE h)))).comp (m P)

def FrobeniusMapContinuous (L : RationalPresentation p S ⥤ RationalPresentation p S)
    (m : FrobeniusMapFamily p S L) : Prop := ∀ P, Continuous (m P)

def FrobeniusMapCoefficient (L : RationalPresentation p S ⥤ RationalPresentation p S)
    (m : FrobeniusMapFamily p S L) : Prop :=
  ∀ P, (m P).comp (chartCoefficient p S P) =
    (chartCoefficient p S (L.obj P)).comp (frobenius p S).toRingHom

/-- The exact source Frobenius laws on specified actual chart objects and maps. -/
class IsFrobeniusCharts
    (L : RationalPresentation p S ⥤ RationalPresentation p S)
    (m : FrobeniusMapFamily p S L) : Prop where
  numerators : FrobeniusNumerators p S L
  denominator : FrobeniusDenominator p S L
  opens : FrobeniusOpens p S φ L
  naturality : FrobeniusMapNaturality p S L m
  continuous : FrobeniusMapContinuous p S L m
  coefficient : FrobeniusMapCoefficient p S L m

variable (O : PeriodSheaf p S)
  (L : RationalPresentation p S ⥤ RationalPresentation p S)
  (m : FrobeniusMapFamily p S L) [C : IsFrobeniusCharts p S φ L m]
  (g : O.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p S φ)).obj O.sheaf)

/-- The sheaf map is fixed by the same actual rational-chart coefficient maps. -/
class IsSheafFrobenius : Prop where
  normalized : ∀ P : RationalPresentation p S,
    g.hom.app (op P.openSet) ≫ O.sheaf.obj.map (eqToHom (C.opens P)).op ≫
      O.rationalComparison.hom.app (op (L.obj P)) =
        O.rationalComparison.hom.app (op P) ≫ CommRingCat.ofHom (m P)

/-- The exact Frobenius endomorphism of the quotient-pushed presheaf. -/
def pushedFrobenius :
    (TopCat.Presheaf.pushforward CommRingCat (quotient p S φ)).obj O.sheaf.obj ⟶
      (TopCat.Presheaf.pushforward CommRingCat (quotient p S φ)).obj O.sheaf.obj :=
  (TopCat.Presheaf.pushforward CommRingCat (quotient p S φ)).map g.hom ≫
    eqToHom ((TopCat.Presheaf.Pushforward.comp_eq
      (frobeniusMap p S φ) (quotient p S φ) O.sheaf.obj).symm.trans
        (TopCat.Presheaf.pushforward_eq' (quotient_frobenius p S φ) O.sheaf.obj))

/-- The corresponding actual sheaf endomorphism. -/
def sheafFrobenius :
    (TopCat.Sheaf.pushforward CommRingCat (quotient p S φ)).obj O.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat (quotient p S φ)).obj O.sheaf :=
  ⟨pushedFrobenius p S φ O g⟩

/-- O_X is the actual invariant-sheaf equalizer on the point quotient. -/
def structureSheaf : TopCat.Sheaf CommRingCat (xSpace p S φ) :=
  equalizer (sheafFrobenius p S φ O g) (𝟙 _)

/-- The fixed inclusion of invariant sections into q_*O_Y. -/
def invariantInclusion : structureSheaf p S φ O g ⟶
    (TopCat.Sheaf.pushforward CommRingCat (quotient p S φ)).obj O.sheaf :=
  equalizer.ι (sheafFrobenius p S φ O g) (𝟙 _)

theorem invariant_frobenius :
    invariantInclusion p S φ O g ≫ sheafFrobenius p S φ O g =
      invariantInclusion p S φ O g := by
  dsimp only [invariantInclusion, structureSheaf]
  exact (equalizer.condition (sheafFrobenius p S φ O g) (𝟙 _)).trans
    (Category.comp_id _)

/-- Its actual ring-category sheaf, for native module sheaves. -/
def ringSheaf : TopCat.Sheaf RingCat (xSpace p S φ) :=
  (sheafCompose (Opens.grothendieckTopology (xSpace p S φ))
    (forget₂ CommRingCat RingCat)).obj (structureSheaf p S φ O g)

/-- Native sheaves of modules on the actual invariant structure sheaf. -/
abbrev Modules := SheafOfModules.{0} (ringSheaf p S φ O g)

/-- Finite locally free modules with actual rank-n stalks. -/
def IsVectorBundle (n : ℕ) (M : Modules p S φ O g) : Prop :=
  M.IsLocallyFree ∧ M.IsFiniteType ∧
    ∀ x : xSpace p S φ,
      Nonempty (Module.Basis (Fin n)
        (↑(TopCat.Presheaf.stalk (structureSheaf p S φ O g).obj x : CommRingCat))
        (↑(TopCat.Presheaf.stalk M.val.presheaf x : AddCommGrpCat.{0})))

/-- The actual bundle groupoid, with native module isomorphisms. -/
abbrev BundleGroupoid (n : ℕ) :=
  Core (ObjectProperty.FullSubcategory (IsVectorBundle p S φ O g n))

end MathlibExt.AlgebraicGeometry.FarguesFontaineSheafModels
