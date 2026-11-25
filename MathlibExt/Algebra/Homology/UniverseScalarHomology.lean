/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-!
# Actual homology transport under lifted-ring scalar restriction

The functor and its complex equivalence are native scalar restriction along
the actual up/down ring equivalence. Cycle and homology comparisons use
native canonical left homology data mapped by the earned exact functor.
Their inclusion and quotient equations are the native universal-property
equations. No cycle, homology, exactness or comparison certificate is supplied.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- The actual native complex functor of scalar restriction. -/
abbrev complexFunctor : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) ⥤
  (ChainComplex (Modules.{u,v} R) ℕ) := (toOriginal.{u,v} R).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The actual native complex equivalence of the up/down ring equivalence. -/
def complexEquivalence : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) ≌
  (ChainComplex (Modules.{u,v} R) ℕ) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (scalarEquiv.{u,v} R)).mapHomologicalComplex
    (ComplexShape.down ℕ)

@[simp]
theorem complexEquivalence_functor :
    (complexEquivalence.{u,v} R).functor = complexFunctor.{u,v} R := rfl

/-- Cycles of the actual mapped complex compare with restriction of the
actual original cycle object. -/
def cyclesComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).cycles n ≅ (toOriginal.{u,v} R).obj (K.cycles n) :=
  ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R)).cyclesIso

/-- Homology of the actual mapped complex compares with restriction of
the actual original homology object. -/
def homologyComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).homology n ≅ (toOriginal.{u,v} R).obj (K.homology n) :=
  ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R)).homologyIso

@[reassoc (attr := simp)]
theorem cyclesComparison_i (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (K.iCycles n) =
      ((complexFunctor.{u,v} R).obj K).iCycles n := by
  exact ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
    ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map (toOriginal.{u,v} R))

@[reassoc (attr := simp)]
theorem quotient_homologyComparison (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj K).homologyπ n ≫ (homologyComparison.{u,v} R K n).hom =
      (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (K.homologyπ n) := by
  exact ((ShortComplex.LeftHomologyData.canonical (K.sc n)).map
    (toOriginal.{u,v} R)).homologyπ_comp_homologyIso_hom

/-- Actual cycle transport is natural under every original chain map. -/
@[reassoc]
theorem cyclesComparison_naturality {K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)} (f : K ⟶ L)
  (n : ℕ) :
    HomologicalComplex.cyclesMap ((complexFunctor.{u,v} R).map f) n ≫
      (cyclesComparison.{u,v} R L n).hom =
    (cyclesComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (HomologicalComplex.cyclesMap f n) := by
  let F := toOriginal.{u,v} R
  let FK := (complexFunctor.{u,v} R).obj K
  let FL := (complexFunctor.{u,v} R).obj L
  let ff := (complexFunctor.{u,v} R).map f
  let eK := cyclesComparison.{u,v} R K n
  let eL := cyclesComparison.{u,v} R L n
  letI : Mono (F.map (L.iCycles n)) := inferInstance
  apply (cancel_mono (F.map (L.iCycles n))).1
  have hl := (Category.assoc _ _ _).trans
    ((congrArg (fun z => HomologicalComplex.cyclesMap ff n ≫ z)
      (cyclesComparison_i.{u,v} R L n)).trans (HomologicalComplex.cyclesMap_i ff n))
  have hr : (eK.hom ≫ F.map (HomologicalComplex.cyclesMap f n)) ≫ F.map (L.iCycles n) =
      FK.iCycles n ≫ F.map (f.f n) := by
    calc
      _ = eK.hom ≫ F.map (HomologicalComplex.cyclesMap f n ≫ L.iCycles n) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z => eK.hom ≫ z) (F.map_comp _ _).symm)
      _ = eK.hom ≫ F.map (K.iCycles n ≫ f.f n) :=
        congrArg (fun z => eK.hom ≫ F.map z) (HomologicalComplex.cyclesMap_i f n)
      _ = (eK.hom ≫ F.map (K.iCycles n)) ≫ F.map (f.f n) :=
        (congrArg (fun z => eK.hom ≫ z) (F.map_comp _ _)).trans
          (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun z => z ≫ F.map (f.f n)) (cyclesComparison_i.{u,v} R K n)
  exact hl.trans hr.symm


/-- Actual homology transport is natural under every original chain map. -/
@[reassoc]
theorem homologyComparison_naturality {K L : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ)}
  (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap ((complexFunctor.{u,v} R).map f) n ≫
      (homologyComparison.{u,v} R L n).hom =
    (homologyComparison.{u,v} R K n).hom ≫ (toOriginal.{u,v} R).map (HomologicalComplex.homologyMap f n) := by
  let F := toOriginal.{u,v} R
  let FK := (complexFunctor.{u,v} R).obj K
  let FL := (complexFunctor.{u,v} R).obj L
  let ff := (complexFunctor.{u,v} R).map f
  let cK := cyclesComparison.{u,v} R K n
  let cL := cyclesComparison.{u,v} R L n
  let eK := homologyComparison.{u,v} R K n
  let eL := homologyComparison.{u,v} R L n
  apply (cancel_epi (FK.homologyπ n)).1
  calc
    _ = (HomologicalComplex.cyclesMap ff n ≫ FL.homologyπ n) ≫ eL.hom :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ eL.hom) (HomologicalComplex.homologyπ_naturality ff n))
    _ = HomologicalComplex.cyclesMap ff n ≫ (cL.hom ≫ F.map (L.homologyπ n)) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => HomologicalComplex.cyclesMap ff n ≫ z)
          (quotient_homologyComparison.{u,v} R L n))
    _ = (cK.hom ≫ F.map (HomologicalComplex.cyclesMap f n)) ≫ F.map (L.homologyπ n) :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ F.map (L.homologyπ n))
          (cyclesComparison_naturality.{u,v} R f n))
    _ = cK.hom ≫ F.map (HomologicalComplex.cyclesMap f n ≫ L.homologyπ n) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => cK.hom ≫ z) (F.map_comp _ _).symm)
    _ = cK.hom ≫ F.map (K.homologyπ n ≫ HomologicalComplex.homologyMap f n) :=
      congrArg (fun z => cK.hom ≫ F.map z) (HomologicalComplex.homologyπ_naturality f n).symm
    _ = (FK.homologyπ n ≫ eK.hom) ≫ F.map (HomologicalComplex.homologyMap f n) :=
      (congrArg (fun z => cK.hom ≫ z) (F.map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ F.map (HomologicalComplex.homologyMap f n))
            (quotient_homologyComparison.{u,v} R K n).symm))
    _ = _ := Category.assoc _ _ _


/-- Homology transport commutes with the literal equality-induced total-degree map. -/
@[reassoc]
theorem homologyComparison_degree_transport (K : (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ))
  {i j : ℕ} (h : i = j) :
    (HomologicalComplex.homologyIsoOfEq ((complexFunctor.{u,v} R).obj K) h).hom ≫
      (homologyComparison.{u,v} R K j).hom =
    (homologyComparison.{u,v} R K i).hom ≫
      (toOriginal.{u,v} R).map (HomologicalComplex.homologyIsoOfEq K h).hom := by
  cases h
  simp

/-- The actual common-world complex is represented over the actual lifted
ring by the native inverse scalar restriction. -/
def toLiftedComplex : (ChainComplex (Modules.{u,v} R) ℕ) ⥤
  (ChainComplex (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ℕ) := (complexEquivalence.{u,v} R).inverse

/-- The actual complex counit identifies restriction of that lifted-ring
representation with the original coefficient complex. -/
def originalComplexIso (K : (ChainComplex (Modules.{u,v} R) ℕ)) :
    (complexFunctor.{u,v} R).obj ((toLiftedComplex.{u,v} R).obj K) ≅ K :=
  (complexEquivalence.{u,v} R).counitIso.app K

/-- Native homology of the actual complex counit compares the two genuine
homology objects, without a universe identification. -/
def originalHomologyIso (K : (ChainComplex (Modules.{u,v} R) ℕ)) (n : ℕ) :
    ((complexFunctor.{u,v} R).obj ((toLiftedComplex.{u,v} R).obj K)).homology n ≅ K.homology n :=
  HomologicalComplex.homologyMapIso (originalComplexIso.{u,v} R K) n

end ModuleCat.UniverseScalarRestriction
