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
# Normalized homology under an additive functor

Let F : C ⥤ D be additive between abelian categories, with independent object and morphism
universes. Write N(Y) for the normalized Moore complex and A(Y) for the alternating face-map
complex of a simplicial object. The Moore inclusion and projection give N(Y) ≃ A(Y) by chain
homotopy equivalence, while additivity gives F(A(Y)) ≅ A(Y ⋙ F).

Combining these comparisons yields F(N(Y)) ≃ N(Y ⋙ F) by chain homotopy equivalence. Its
induced isomorphisms H_i(F(N(Y))) ≅ H_i(N(Y ⋙ F)) are natural in simplicial maps, for every i
: ℕ. When F preserves homology, a quasi-isomorphism of normalized simplicial maps remains a
quasi-isomorphism after whiskering by F.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor

universe uC vC uD vD

namespace AlgebraicTopology.DoldKan

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- Normalize a simplicial object and then apply an additive functor.

For additive F : C ⥤ D between abelian categories, mappedNormalizedFunctor sends Y to the
chain complex F(N(Y)) and a simplicial map to its normalized chain map followed by degreewise
F. -/
abbrev mappedNormalizedFunctor : SimplicialObject C ⥤ ChainComplex D ℕ :=
  normalizedMooreComplex C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ)

/-- Normalize a simplicial object after applying its coefficient functor.

For additive F : C ⥤ D between abelian categories, whiskeredNormalizedFunctor sends Y to N(Y ⋙
F), the Moore complex of the simplicial diagram obtained by applying F degreewise. -/
abbrev whiskeredNormalizedFunctor : SimplicialObject C ⥤ ChainComplex D ℕ :=
  (SimplicialObject.whiskering C D).obj F ⋙ normalizedMooreComplex D

/-- Homotopy equivalence for additive normalization transport.

For a simplicial object Y and additive F between abelian categories, compose F applied to the
Moore-to-alternating homotopy equivalence, the alternating-complex functor comparison, and the
inverse Moore-to-alternating comparison for Y ⋙ F. This gives F(N(Y)) ≃ N(Y ⋙ F) by chain
homotopy equivalence. -/
def mappedNormalizedHomotopyEquiv (Y : SimplicialObject C) :
    HomotopyEquiv ((mappedNormalizedFunctor F).obj Y)
      ((whiskeredNormalizedFunctor F).obj Y) :=
  (F.mapHomotopyEquiv
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y))).trans
    ((HomotopyEquiv.ofIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso F).app Y)).trans
      (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y ⋙ F)).symm)

/-- Moore inclusion after degreewise additive transport.

For additive F : C ⥤ D, the natural Moore inclusion N(Y) → A(Y) induces a natural chain map
F(N(Y)) → F(A(Y)) by applying F degreewise. -/
def mappedNormalizationInclusion :
    mappedNormalizedFunctor F ⟶
      alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex (ComplexShape.down ℕ) :=
  whiskerRight (inclusionOfMooreComplex C) (F.mapHomologicalComplex (ComplexShape.down ℕ))

/-- Moore inclusion of a transported simplicial diagram.

For additive F : C ⥤ D, apply the Moore inclusion to Y ⋙ F. This gives a natural chain map N(Y
⋙ F) → A(Y ⋙ F). -/
def whiskeredNormalizationInclusion :
    whiskeredNormalizedFunctor F ⟶
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D :=
  whiskerLeft ((SimplicialObject.whiskering C D).obj F) (inclusionOfMooreComplex D)

/-- Homology isomorphism of the transported Moore inclusion.

For additive F between abelian categories and i : ℕ, the chain map F(N(Y)) → F(A(Y)) induced
by Moore inclusion gives a natural isomorphism H_i(F(N(Y))) ≅ H_i(F(A(Y))). It comes from the
transported chain homotopy equivalence. -/
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

/-- Homology isomorphism of the whiskered Moore inclusion.

For a simplicial object Y and additive F between abelian categories, Moore inclusion on Y ⋙ F
gives H_i(N(Y ⋙ F)) ≅ H_i(A(Y ⋙ F)), naturally in Y for every natural degree i. -/
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

/-- Natural homology comparison for additive normalization.

For additive F : C ⥤ D between abelian categories, the two Moore inclusion comparisons and
F(A(Y)) ≅ A(Y ⋙ F) yield a natural isomorphism H_i(F(N(Y))) ≅ H_i(N(Y ⋙ F)) for every i : ℕ. -/
def mappedNormalizedHomologyNatIso (i : ℕ) :
    mappedNormalizedFunctor F ⋙ HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i ≅
      whiskeredNormalizedFunctor F ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i :=
  mappedInclusionHomologyIso F i ≪≫
    isoWhiskerRight (alternatingFaceMapComplexCompMapHomologicalComplexIso F)
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i) ≪≫
    (whiskeredInclusionHomologyIso F i).symm

/-- Component of the additive normalized-homology comparison.

At Y, the component of mappedNormalizedHomologyNatIso F i is precisely the degree-i homology
isomorphism induced by mappedNormalizedHomotopyEquiv F Y. -/
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

/-- Naturality square for normalized homology after additive transport.

For a simplicial map φ : Y → Z and additive F between abelian categories, let χ_W :
H_i(F(N(W))) ≅ H_i(N(W ⋙ F)) be the comparison for W = Y,Z. Then H_i(F(N(φ))) ≫ χ_Z.hom =
χ_Y.hom ≫ H_i(N(φ ⋙ F)). -/
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

/-- Quasi-isomorphism of normalized maps preserved by a homology-preserving functor.

Let F : C ⥤ D be additive between abelian categories and preserve homology. If N(φ) is a
quasi-isomorphism for a simplicial map φ : Y → Z in C, then N(φ ⋙ F) is a quasi-isomorphism in
D. -/
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
