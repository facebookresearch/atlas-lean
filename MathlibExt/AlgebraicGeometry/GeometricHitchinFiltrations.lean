/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedBettiDirectImages
public import MathlibExt.AlgebraicGeometry.RankTwoHitchinModels
public import MathlibExt.AlgebraicGeometry.NormalCrossingsModels

/-!
# Independent geometric weight and Hitchin perverse filtrations

The geometric weight filtration comes from an actual smooth proper SNC
compactification j and ordinary truncation of the native Rj_*Q. Its
cohomological index is k-d. The perverse filtration comes from the actual
Hitchin map, the native Rchi_*Q[a], middle perverse truncation at k, and
hypercohomology in degree d-a. Here a is the number of actual Hitchin
section coordinates, equal to 4g-3. Both images use the normalized native
derived-adjunction cohomology comparison and canonical shift maps.

The weight operator has no dependence on the Hitchin map, a perverse
theory, or a nonabelian Hodge map.

Sources: Deligne, Theorie de Hodge II, Sections 3.1.5--3.1.9 and
3.2.1--3.2.5, Proposition 3.1.8 and Theorem 3.2.5;
dCHM arXiv:1004.1420v2, Section 1.4.1 and Theorem 1.1.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricHitchinFiltrations

open _root_.CategoryTheory _root_.AlgebraicGeometry
open ComplexAnalytification PerverseSheaves BettiRealization
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHitchinModels
open BoundedBettiDirectImages

attribute [local instance] HasDerivedCategory.standard

/-- An actual compactification with its genuine reduced strict-crossings boundary. -/
structure SNCCompactification (X : RankTwoHiggsCurveFamilies.ComplexScheme) where
  scheme : RankTwoHiggsCurveFamilies.ComplexScheme
  variety : IsComplexVariety scheme
  proper : IsProper scheme.hom
  smooth : Smooth scheme.hom
  inclusion : X ⟶ scheme
  openImmersion : IsOpenImmersion inclusion.left
  dense : DenseRange inclusion.left
  boundary : scheme.left.IdealSheafData
  crossings : NormalCrossingsModels.IsStrictNormalCrossings scheme boundary
  complement : (boundary.support : Set scheme.left) = (Set.range inclusion.left)ᶜ

/-- Deligne's cohomological shift of the independent geometric truncation filtration. -/
def weightMap {X : RankTwoHiggsCurveFamilies.ComplexScheme} (J : SNCCompactification X)
    (A : BoundedDerivedAdjunction (spaceMap J.inclusion)) (k d : ℤ) :
    Hypercohomology (space J.scheme)
      ((DerivedCategory.TStructure.t.truncLE (k - d)).obj
        (constantDirectImage (spaceMap J.inclusion))) d →ₗ[ℚ] Cohomology (space X) d :=
  cohomologyComparison A d ∘ₗ
    hypercohomologyMap
      ((DerivedCategory.TStructure.t.truncLEι (k - d)).app
        (constantDirectImage (spaceMap J.inclusion))) d

def weightFiltration {X : RankTwoHiggsCurveFamilies.ComplexScheme} (J : SNCCompactification X)
    (A : BoundedDerivedAdjunction (spaceMap J.inclusion)) (k d : ℤ) :
    Submodule ℚ (Cohomology (space X) d) := (weightMap J A k d).range

/-- The canonical addition of shifts from degree d-a back to degree d. -/
def shiftHypercohomology {Y : TopCat.{0}} (K : RationalDerived Y) (a d : ℤ) :
    Hypercohomology Y (K⟦a⟧) (d - a) →ₗ[ℚ] Hypercohomology Y K d where
  toFun b := b ≫ (shiftFunctorAdd' (RationalDerived Y) a (d - a) d (by omega)).inv.app K
  map_add' b c := by simp [Preadditive.add_comp]
  map_smul' r b := by simp [Linear.smul_comp]

variable (C : RankTwoHiggsCurveFamilies.ComplexScheme)
    [CoherentCurveLinearSeries.IsProperCurve C.hom]
  [CoherentCurveLinearSeries.HasConstantGlobalSections C.hom] (B : BaseChanges C)
    (M : ModuliModel C B)
  (S : SectionBases C) (H : HitchinModel C B M S)

def shiftedHitchinComplex : RationalDerived (space (base C)) :=
  (constantDirectImage (spaceMap H.map))⟦(baseDimension C : ℤ)⟧

def perverseObject
    (h : PerverseSheaves.boundedConstructible (base C) (shiftedHitchinComplex C B M S H)) :
    (PerverseSheaves.boundedConstructible (base C)).FullSubcategory :=
  ⟨shiftedHitchinComplex C B M S H, h⟩

variable [IsComplexVariety (base C)] [PerverseSheafTheory (base C)]

/-- The source perverse index on Rchi_*Q[a], with hypercohomological degree d-a. -/
def perverseMap
    (A : BoundedDerivedAdjunction (spaceMap H.map))
    (h : PerverseSheaves.boundedConstructible (base C) (shiftedHitchinComplex C B M S H))
    (k d : ℤ) :
    Hypercohomology (space (base C))
      (((perverseTStructure (base C)).truncLE k).obj (perverseObject C B M S H h)).obj
        (d - (baseDimension C : ℤ)) →ₗ[ℚ] Cohomology (space M.scheme) d :=
  cohomologyComparison A d ∘ₗ
    shiftHypercohomology (constantDirectImage (spaceMap H.map)) (baseDimension C) d ∘ₗ
      hypercohomologyMap
        (((perverseTStructure (base C)).truncLEι k).app (perverseObject C B M S H h)).hom
          (d - (baseDimension C : ℤ))

def perverseFiltration
    (A : BoundedDerivedAdjunction (spaceMap H.map))
    (h : PerverseSheaves.boundedConstructible (base C) (shiftedHitchinComplex C B M S H))
    (k d : ℤ) : Submodule ℚ (Cohomology (space M.scheme) d) :=
  (perverseMap C B M S H A h k d).range

end MathlibExt.AlgebraicGeometry.GeometricHitchinFiltrations
