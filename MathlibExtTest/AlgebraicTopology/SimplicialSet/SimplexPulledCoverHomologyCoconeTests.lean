/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexPulledCoverHomologyCocone

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u

#check SSet.KanComplex.simplexLiftToPulledCover
#print axioms SSet.KanComplex.simplexLiftToPulledCover
#check SSet.KanComplex.simplexLiftToPulledCover_fst
#print axioms SSet.KanComplex.simplexLiftToPulledCover_fst
#check SSet.KanComplex.simplexLiftToPulledCover_snd
#print axioms SSet.KanComplex.simplexLiftToPulledCover_snd
#check SSet.KanComplex.simplexLiftToPulledCover_pairMap
#print axioms SSet.KanComplex.simplexLiftToPulledCover_pairMap
#check SSet.KanComplex.simplexLiftToPulledCover_isPullback
#print axioms SSet.KanComplex.simplexLiftToPulledCover_isPullback
#check SSet.KanComplex.nativeSimplexLifts_exists_deck
#print axioms SSet.KanComplex.nativeSimplexLifts_exists_deck
#check SSet.KanComplex.simplexLiftToPulledCover_deck
#print axioms SSet.KanComplex.simplexLiftToPulledCover_deck
#check SSet.KanComplex.simplexLiftToPulledCover_transition
#print axioms SSet.KanComplex.simplexLiftToPulledCover_transition
#check SSet.simplexFibrationHomologyCoefficients
#print axioms SSet.simplexFibrationHomologyCoefficients
#check SSet.simplexLiftToPulledCover_homologyMap_independent
#print axioms SSet.simplexLiftToPulledCover_homologyMap_independent
#check SSet.simplexPulledCoverHomologyCocone
#print axioms SSet.simplexPulledCoverHomologyCocone
#check SSet.simplexLiftToPulledCover_mem_realizationWeakEquivalences
#print axioms SSet.simplexLiftToPulledCover_mem_realizationWeakEquivalences
#check SSet.simplexPulledCoverHomologyCocone_ι_isIso
#print axioms SSet.simplexPulledCoverHomologyCocone_ι_isIso
#check SSet.simplexFibrationHomologyCoefficients_map_isIso
#print axioms SSet.simplexFibrationHomologyCoefficients_map_isIso
#check SSet.simplexFibrationRootAction_isTrivial
#print axioms SSet.simplexFibrationRootAction_isTrivial

namespace SimplexPulledCoverHomologyCoconeTests

open SSet.KanComplex

example {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
    (v : E ⟶ E') (hv : v ≫ q = p) (b : B _⦋0⦌)
    {A : SimplexCategory} (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ B)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ SSet.KanComplex.nativeCover B b //
      L ≫ SSet.KanComplex.nativeCoverProjection B b = σ}) :
    (SSet.simplexPullbackDiagramMap v hv).app (CostructuredArrow.mk σ) ≫
        SSet.KanComplex.simplexLiftToPulledCover q b σ L =
      SSet.KanComplex.simplexLiftToPulledCover p b σ L ≫
        SSet.KanComplex.nativeCoverBaseChangeMap v hv b :=
  SSet.KanComplex.simplexLiftToPulledCover_pairMap v hv b σ L

example {B : SSet.{u}} [SSet.KanComplex B] (b : B _⦋0⦌) {n : ℕ}
    (σ : (Δ[n] : SSet.{u}) ⟶ B)
    (L K : {L : (Δ[n] : SSet.{u}) ⟶ nativeCover B b // L ≫ nativeCoverProjection B b = σ}) :
    ∃ g : End (SSet.FundamentalGroupoid.mk b), nativeCoverDeckedSimplexLift b g σ L = K :=
  nativeSimplexLifts_exists_deck b σ L K

variable (G : Type u) [Groupoid.{u} G] [CategoryTheory.IsConnected G]
  {E : SSet.{u}} (p : E ⟶ CategoryTheory.nerve G)
  (b : (CategoryTheory.nerve G) _⦋0⦌) (R : AddCommGrpCat.{u}) (n : ℕ)

example {A : SimplexCategory}
    (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ CategoryTheory.nerve G)
    (L K : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover (CategoryTheory.nerve G) b //
      L ≫ nativeCoverProjection (CategoryTheory.nerve G) b = σ})
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _) :
    SSet.homologyMap (simplexLiftToPulledCover p b σ L) R n =
      SSet.homologyMap (simplexLiftToPulledCover p b σ K) R n :=
  SSet.simplexLiftToPulledCover_homologyMap_independent G p b R n σ L K hDeck

example [Fibration p] {A : SimplexCategory}
    (σ : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ CategoryTheory.nerve G)
    (L : {L : (SSet.stdSimplex.obj A : SSet.{u}) ⟶ nativeCover (CategoryTheory.nerve G) b //
      L ≫ nativeCoverProjection (CategoryTheory.nerve G) b = σ}) :
    SSet.realizationWeakEquivalences (simplexLiftToPulledCover p b σ L) :=
  SSet.simplexLiftToPulledCover_mem_realizationWeakEquivalences G p b σ L

example [Fibration p]
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _)
    (i : SSet.SimplexIndex (CategoryTheory.nerve G)) :
    IsIso ((SSet.simplexPulledCoverHomologyCocone G p b R n hDeck).ι.app i) :=
  SSet.simplexPulledCoverHomologyCocone_ι_isIso G p b R n hDeck i

example [Fibration p] {i j : SSet.SimplexIndex (CategoryTheory.nerve G)} (a : i ⟶ j) :
    IsIso ((SSet.simplexFibrationHomologyCoefficients G p R n).map a) :=
  SSet.simplexFibrationHomologyCoefficients_map_isIso G p R n a

example [Fibration p]
    [∀ {s t : SSet.SimplexIndex (CategoryTheory.nerve G)} (a : s ⟶ t),
      IsIso ((SSet.simplexFibrationHomologyCoefficients G p R n).map a)]
    (hDeck : ∀ g : End (SSet.FundamentalGroupoid.mk b),
      SSet.homologyMap (nativeCoverBaseChangeDeckMap p b g) R n = 𝟙 _)
    (i : SSet.SimplexIndex (CategoryTheory.nerve G)) :
    Representation.IsTrivial
      (invertingCoefficientRootAction (SSet.simplexFibrationHomologyCoefficients G p R n) i) :=
  SSet.simplexFibrationRootAction_isTrivial G p b R n hDeck i

end SimplexPulledCoverHomologyCoconeTests
