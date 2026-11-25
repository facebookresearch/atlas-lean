/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Actual normalized homology under an additive functor

Native Dold–Kan and native alternating-functor transport compare
F(N(Y)) with N(Y⋙F) by a homotopy equivalence.  The resulting homology
isomorphism is natural in the original simplicial map.  No kernel
preservation is used for that comparison.

When F actually preserves homology, a given original normalized
quasi-isomorphism remains a quasi-isomorphism after applying F to its
simplicial diagram.  This is the generic native transport needed before
flat scalar extension of an actual polynomial resolution can be claimed.
Native verification is unexecuted for this source proposal.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor

universe uC vC uD vD

namespace AlgebraicTopology.DoldKan

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- Native normalization is functorial after mapping the actual simplicial diagram. -/
abbrev mappedNormalizedFunctor : SimplicialObject C ⥤ ChainComplex D ℕ :=
  normalizedMooreComplex C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ)

abbrev whiskeredNormalizedFunctor : SimplicialObject C ⥤ ChainComplex D ℕ :=
  (SimplicialObject.whiskering C D).obj F ⋙ normalizedMooreComplex D

/-- Actual native Dold–Kan and alternating transport, requiring only additivity. -/
def mappedNormalizedHomotopyEquiv (Y : SimplicialObject C) :
    HomotopyEquiv ((mappedNormalizedFunctor F).obj Y)
      ((whiskeredNormalizedFunctor F).obj Y) :=
  (F.mapHomotopyEquiv
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y))).trans
    ((HomotopyEquiv.ofIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y)).trans
      (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y ⋙ F)).symm)

/-- The actual source inclusion after applying the additive functor. -/
def mappedNormalizationInclusion :
    mappedNormalizedFunctor F ⟶
      alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) :=
  whiskerRight (inclusionOfMooreComplex C) (F.mapHomologicalComplex (ComplexShape.down ℕ))

/-- The actual target inclusion on the mapped simplicial diagram. -/
def whiskeredNormalizationInclusion :
    whiskeredNormalizedFunctor F ⟶
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D :=
  whiskerLeft ((SimplicialObject.whiskering C D).obj F) (inclusionOfMooreComplex D)

/-- Mapped native normalization gives the natural actual homology comparison. -/
def mappedInclusionHomologyIso (i : ℕ) :
    mappedNormalizedFunctor F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i ≅
      (alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ)) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i :=
  NatIso.ofComponents
    (fun Y => (F.mapHomotopyEquiv
      (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y))).toHomologyIso i)
    (by
      intro Y Z φ
      exact (whiskerRight (mappedNormalizationInclusion F)
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i)).naturality φ)

/-- Native target normalization gives the actual natural homology comparison. -/
def whiskeredInclusionHomologyIso (i : ℕ) :
    whiskeredNormalizedFunctor F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i ≅
      ((SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i :=
  NatIso.ofComponents
    (fun Y => (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := Y ⋙ F)).toHomologyIso i)
    (by
      intro Y Z φ
      exact (whiskerRight (whiskeredNormalizationInclusion F)
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i)).naturality φ)

/-- H(F(NY)) and H(N(Y⋙F)) are naturally isomorphic, without an exactness assumption. -/
def mappedNormalizedHomologyNatIso (i : ℕ) :
    mappedNormalizedFunctor F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i ≅
      whiskeredNormalizedFunctor F ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i :=
  mappedInclusionHomologyIso F i ≪≫
    isoWhiskerRight (alternatingFaceMapComplexCompMapHomologicalComplexIso F)
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i) ≪≫
    (whiskeredInclusionHomologyIso F i).symm

/-- The natural comparison is the homology map of the constructed native homotopy equivalence. -/
theorem mappedNormalizedHomologyNatIso_app (i : ℕ) (Y : SimplicialObject C) :
    (mappedNormalizedHomologyNatIso F i).app Y =
      (mappedNormalizedHomotopyEquiv F Y).toHomologyIso i := by
  apply Iso.ext
  change HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap Y)) i ≫
        HomologicalComplex.homologyMap
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app Y) i ≫
            HomologicalComplex.homologyMap (PInftyToNormalizedMooreComplex (Y ⋙ F)) i =
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap Y) ≫
        ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom.app Y ≫
          PInftyToNormalizedMooreComplex (Y ⋙ F))) i
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]

private def whiskeredNormalizationProjection :
    (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D ⟶
      whiskeredNormalizedFunctor F where
  app Y := PInftyToNormalizedMooreComplex (Y ⋙ F)
  naturality {Y Z} φ :=
    PInftyToNormalizedMooreComplex_naturality (Functor.whiskerRight φ F)

private def mappedNormalizedComparison :
    mappedNormalizedFunctor F ⟶ whiskeredNormalizedFunctor F :=
  mappedNormalizationInclusion F ≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso F).hom ≫
      whiskeredNormalizationProjection F

/-- The actual normalized homology square is natural in the original simplicial operator. -/
@[reassoc]
theorem mappedNormalizedHomology_naturality {Y Z : SimplicialObject C} (φ : Y ⟶ Z) (i : ℕ) :
    HomologicalComplex.homologyMap ((mappedNormalizedFunctor F).map φ) i ≫
        ((mappedNormalizedHomotopyEquiv F Z).toHomologyIso i).hom =
      ((mappedNormalizedHomotopyEquiv F Y).toHomologyIso i).hom ≫
        HomologicalComplex.homologyMap ((whiskeredNormalizedFunctor F).map φ) i := by
  have h := (mappedNormalizedComparison F).naturality φ
  change (mappedNormalizedFunctor F).map φ ≫ (mappedNormalizedHomotopyEquiv F Z).hom =
    (mappedNormalizedHomotopyEquiv F Y).hom ≫ (whiskeredNormalizedFunctor F).map φ at h
  change HomologicalComplex.homologyMap ((mappedNormalizedFunctor F).map φ) i ≫
      HomologicalComplex.homologyMap (mappedNormalizedHomotopyEquiv F Z).hom i =
    HomologicalComplex.homologyMap (mappedNormalizedHomotopyEquiv F Y).hom i ≫
      HomologicalComplex.homologyMap ((whiskeredNormalizedFunctor F).map φ) i
  exact (HomologicalComplex.homologyMap_comp ((mappedNormalizedFunctor F).map φ)
    (mappedNormalizedHomotopyEquiv F Z).hom i).symm.trans
      ((congrArg (fun m => HomologicalComplex.homologyMap m i) h).trans
        (HomologicalComplex.homologyMap_comp (mappedNormalizedHomotopyEquiv F Y).hom
          ((whiskeredNormalizedFunctor F).map φ) i))

/-- A normalized simplicial map stays a quasi-isomorphism under an actually exact functor.
The hypothesis is the original source map's quasi-isomorphism, not a desired mapped result. -/
theorem quasiIso_normalizedMap_of_preservesHomology [F.PreservesHomology]
    {Y Z : SimplicialObject C} (φ : Y ⟶ Z)
    (hφ : QuasiIso ((normalizedMooreComplex C).map φ)) :
    QuasiIso ((normalizedMooreComplex D).map (whiskerRight φ F)) := by
  haveI : QuasiIso ((normalizedMooreComplex C).map φ) := hφ
  haveI : QuasiIso ((mappedNormalizedFunctor F).map φ) := by
    change QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((normalizedMooreComplex C).map φ))
    infer_instance
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso ((whiskeredNormalizedFunctor F ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).map φ)
  apply (NatIso.isIso_map_iff (mappedNormalizedHomologyNatIso F i) φ).mp
  change IsIso (HomologicalComplex.homologyMap ((mappedNormalizedFunctor F).map φ) i)
  infer_instance

end AlgebraicTopology.DoldKan

end
