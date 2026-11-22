/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.DiagonalHomotopy
import MathlibExt.CategoryTheory.Enriched.Ordinary.FunctorCategory

import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.IntegerColimitNormalization
import MathlibExt.Algebra.Category.Grp.FilteredSourceTypeColimit
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionTelescopePi
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeGroups
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LoopTailAllPointComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalTelescopeOmegaHomRetract
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionOmegaTelescope

/-!
# Integer homotopy detection of orthogonal Omega tests

The corrected function-iteration diagrams identify their group and Type colimits with the signed integer homotopy functors of the sequential restriction. If a native orthogonal arrow induces isomorphisms in every integer degree, its function-telescope map is level weak and precomposition into every Omega target is bijective in the level homotopy category. This yields the original Omega-test weak class.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open FunctionSpectrum FunctionIteration OriginalRawIndexCorrection OriginalSequentialFunctionChart
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
/-- The original orthogonal index category for raw iteration. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original monoidal structure on orthogonal indices for raw iteration. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indices for raw iteration. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}

/-- The actual original sequential restriction, through both complete native index maps. -/
abbrev j : Carrier.{u, v} ⥤ PointedCGWH.SequentialSpectrum.{u, v} :=
  restriction sequentialOrthogonalOperatorIndexFunctor.{u, v}

/-- Every actual j level and full input map is the original native level functor. -/
theorem j_level (m : ℕ) : j.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m =
    IterationMaps.level m := by
  refine CategoryTheory.Functor.ext (F := j.{u, v} ⋙ PointedCGWH.SequentialSpectrum.evaluation m)
    (G := IterationMaps.level.{u, v} m) (fun X => rfl) (h_map := ?_)
  intro X Y f
  change component (restrictionMap sequentialOrthogonalOperatorIndexFunctor f)
      (HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.sequentialDegree m) =
    eqToHom rfl ≫ component f (OrthogonalOperatorIndex.ofIndex.{u, v} m) ≫ eqToHom rfl
  have hComp := restrictionMap_component sequentialOrthogonalOperatorIndexFunctor f
    (HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.sequentialDegree m)
  change component (restrictionMap sequentialOrthogonalOperatorIndexFunctor f)
      (HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.sequentialDegree m) =
    component f (OrthogonalOperatorIndex.ofIndex.{u, v} m) at hComp
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hComp

/-- Both original loop-power constructors retain the identical full pointed functor. -/
theorem loopPower_same (n : ℕ) :
    PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n = LoopPowerAtPoints.power n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n ⋙ PointedCGWH.loop =
      LoopPowerAtPoints.power n ⋙ PointedCGWH.loop
    exact congrArg (fun P => P ⋙ PointedCGWH.loop) ih

/-- Both original loop-count functors are carried through the proved whole functor equality. -/
def loopComparison (n : ℕ) : PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n ≅
    LoopPowerAtPoints.power n := eqToIso (loopPower_same n)

/-- The complete actual j map retains the same original level component. -/
theorem j_level_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap (j.map f) m = (IterationMaps.level m).map f := by
  have h := restrictionMap_component sequentialOrthogonalOperatorIndexFunctor f
    (HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.sequentialDegree m)
  change PointedCGWH.SequentialSpectrum.levelMap (j.map f) m = (IterationMaps.level m).map f at h
  exact h

universe uA vA
private theorem composeMapSquares {K : Type uA} [Category.{vA} K]
    {A B C D E F : K} (u : A ⟶ B) (a : A ⟶ C) (a' : B ⟶ D)
    (v : C ⟶ D) (b : C ⟶ E) (b' : D ⟶ F) (w : E ⟶ F)
    (h1 : u ≫ a' = a ≫ v) (h2 : v ≫ b' = b ≫ w) :
    u ≫ (a' ≫ b') = (a ≫ b) ≫ w :=
  (Category.assoc u a' b').symm.trans
    ((congrArg (fun h => h ≫ b') h1).trans
      ((Category.assoc a v b').trans
        ((congrArg (fun h => a ≫ h) h2).trans (Category.assoc a b w).symm)))

/-- Every original ell isometry is natural for every full native spectrum arrow. -/
def indexValueNatIso (n m : ℕ) : IterationMaps.level.{u, v} (m + n) ≅
    IterationMaps.level (m + n) :=
  NatIso.ofComponents (F := IterationMaps.level.{u, v} (m + n))
    (G := IterationMaps.level.{u, v} (m + n))
    (fun (X : Carrier.{u, v}) => (RightShift.bare X).mapIso (ell n m))
    (fun {X Y : Carrier.{u, v}} (f : X ⟶ Y) => by
    change component f (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n)) ≫
        (RightShift.bare Y).map (ell n m).hom =
      (RightShift.bare X).map (ell n m).hom ≫
        component f (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))
    have h := (ordinaryNatTrans ((OrthogonalSourceRightModule.restrictionFunctor.{u, v}).map f)).naturality
      (ell n m).hom
    simpa only [RightShift.bare, EnrichedFunctor.toOrdinaryFunctor_obj,
      ordinaryNatTrans_app, OrthogonalSourceRightModule.restrictionFunctor_obj,
      OrthogonalSourceRightModule.restrictionFunctor_map_component,
      Functor.mapIso_hom] using h.symm)

/-- Original sequential evaluation retains its full component and input naturality after actual j. -/
def sequentialEvaluation (n m : ℕ) :
    j.{u, v} ⋙ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n ⋙ PointedCGWH.SequentialSpectrum.evaluation m) ≅
      IterationMaps.level (m + n) ⋙ LoopPowerAtPoints.power n :=
  NatIso.ofComponents
    (fun X => (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).app (j.obj X) ≪≫
      (loopComparison n).app (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))))
    (fun {X Y} f => by
      let P := PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n
      let Q := LoopPowerAtPoints.power.{u, v} n
      let a := (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X)
      let a' := (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj Y)
      let g := (IterationMaps.level (m + n)).map f
      have hOld := (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.naturality (j.map f)
      have hMap := j_level_map f (m + n)
      have h1 := hOld.trans (congrArg (fun g => a ≫ P.map g) hMap)
      have h2 := (loopComparison n).hom.naturality g
      exact composeMapSquares
        (PointedCGWH.SequentialSpectrum.levelMap
          ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n).map (j.map f)) m)
        a a' (P.map g)
        ((loopComparison n).hom.app (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))))
        ((loopComparison n).hom.app (Y.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))))
        (Q.map g) h1 h2)

/-- The original evaluated native maps retain the entire genuine ell value Iso. -/
def correctedEvaluation (n m : ℕ) :
    IterationMaps.power.{u, v} n ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + n) ⋙ LoopPowerAtPoints.power n :=
  IterationMaps.evaluationComparison n m ≪≫
    Functor.isoWhiskerRight (indexValueNatIso n m) (LoopPowerAtPoints.power n)

/-- Both native evaluated maps and the genuine ell word compare with the same original sequential stage. -/
def stagePointedNatIso (n m : ℕ) :
    IterationMaps.power.{u, v} n ⋙ IterationMaps.level m ≅
      j ⋙ (PointedCGWH.SequentialSpectrum.OrderedLoop.iterate n ⋙ PointedCGWH.SequentialSpectrum.evaluation m) :=
  correctedEvaluation n m ≪≫ (sequentialEvaluation n m).symm

/-- The original input transition retains F^n(eta_X) and its actual whole prefix map. -/
theorem inputTransition_component (eta : 𝟭 Carrier.{u, v} ⟶ IterationMaps.shiftedLoop)
    (n m : ℕ) (X : Carrier.{u, v}) :
    (IterationMaps.level m).map ((Functor.Iteration.inputTransition eta n).app X) =
      (IterationMaps.level m).map ((IterationMaps.power n).map (eta.app X)) ≫
        (IterationMaps.level m).map
          (eqToHom (Functor.congr_obj
            (Functor.Iteration.iterate_succ_prefix IterationMaps.shiftedLoop n).symm X)) := by
  rw [Functor.Iteration.inputTransition_app, Functor.map_comp]

/-- Every original input coaugmentation has both full evaluated native transition maps. -/
theorem inputTransition_evaluation (eta : 𝟭 Carrier.{u, v} ⟶ IterationMaps.shiftedLoop)
    (n m : ℕ) (X : Carrier.{u, v}) :
    (IterationMaps.level m).map ((Functor.Iteration.inputTransition eta n).app X) ≫
        (IterationMaps.evaluationComparison (n + 1) m).hom.app X =
      (IterationMaps.evaluationComparison n m).hom.app X ≫
        (LoopPowerAtPoints.power n).map ((IterationMaps.level (m + n)).map (eta.app X)) ≫
          (IterationMaps.prefixEvaluation n m).hom.app X := by
  have hPrefix := congrArg (fun e => e.hom.app X) (IterationMaps.evaluationComparison_prefix n m)
  have hNatural := IterationMaps.evaluationComparison_hom_naturality n m (eta.app X)
  rw [inputTransition_component, Category.assoc]
  change (IterationMaps.level m).map
      ((Functor.Iteration.iteratePrefixIso IterationMaps.shiftedLoop n).inv.app X) ≫
        (IterationMaps.evaluationComparison (n + 1) m).hom.app X =
    (IterationMaps.evaluationComparison n m).hom.app (IterationMaps.shiftedLoop.obj X) ≫
      (IterationMaps.prefixEvaluation n m).hom.app X at hPrefix
  rw [← Functor.Iteration.iteratePrefixIso_inv_app]
  rw [hPrefix, ← Category.assoc, hNatural, Category.assoc]
  rfl

/-- Both original count maps are the full equality Iso for the same one-loop prefix. -/
def loopPrefix (n : ℕ) : LoopPowerAtPoints.power.{u, v} (n + 1) ≅
    PointedCGWH.loop ⋙ LoopPowerAtPoints.power n :=
  eqToIso (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n)

/-- The actual continuous lower cast has the same entire original value transport. -/
theorem lowerCast_value (X : Carrier.{u, v}) (n m : ℕ) :
    (RightShift.bare X).map (lowerCast n m).inv =
      eqToHom (congrArg (RightShift.bare X).obj (Nat.add_assoc m n 1)) := by
  change (RightShift.bare X).map (eqToHom (Nat.add_assoc m n 1)) = _
  exact eqToHom_map (RightShift.bare X) (Nat.add_assoc m n 1)

/-- The whole native prefix keeps its original lower cast and both genuine loop-count maps. -/
theorem prefixEvaluation_decomposition (X : Carrier.{u, v}) (n m : ℕ) :
    (IterationMaps.prefixEvaluation n m).hom.app X =
      (LoopPowerAtPoints.power n).map
        (PointedCGWH.loop.map ((RightShift.bare X).map (lowerCast n m).inv)) ≫
          (loopPrefix n).inv.app
            (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))) := by
  let P := LoopPowerAtPoints.power.{u, v} n
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let h := Nat.add_assoc m n 1
  let hValue := congrArg (RightShift.bare X).obj h
  let p := ((congrArg (fun H => H ⋙ P) (IterationMaps.stepEvaluation_eq (m + n))).trans
    ((congrArg (fun H => IterationMaps.level (m + n + 1) ⋙ H)
      (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm).trans
      (congrArg (fun k => IterationMaps.level k ⋙ LoopPowerAtPoints.power (n + 1)) h)))
  have h0 : (IterationMaps.prefixEvaluation n m).hom.app X =
      eqToHom (Functor.congr_obj p X) := eqToHom_app p X
  have h1 := lowerCast_value X n m
  have h2 := eqToHom_map PointedCGWH.loop hValue
  have h3 := eqToHom_map P (congrArg PointedCGWH.loop.obj hValue)
  have hMapped : P.map (PointedCGWH.loop.map ((RightShift.bare X).map (lowerCast n m).inv)) =
      eqToHom (congrArg P.obj (congrArg PointedCGWH.loop.obj hValue)) :=
    (congrArg (fun g => P.map (PointedCGWH.loop.map g)) h1).trans
      ((congrArg P.map h2).trans h3)
  have hInv : (loopPrefix n).inv.app T =
      eqToHom (Functor.congr_obj (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm T) :=
    eqToHom_app (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm T
  have hRight := congrArg₂ (fun f g => f ≫ g) hMapped hInv
  have hJoin := eqToHom_trans
    (congrArg P.obj (congrArg PointedCGWH.loop.obj hValue))
    (Functor.congr_obj (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm T)
  exact h0.trans (hJoin.symm.trans hRight.symm)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open FunctionSpectrum FunctionIteration OriginalRawIndexCorrection OriginalSequentialFunctionChart
open scoped MonoidalClosed
/-- The original orthogonal index category for corrected prefix evaluation. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original monoidal structure on orthogonal indices for corrected prefix evaluation. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indices for corrected prefix evaluation. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

universe uC vC

private theorem mapPrefixSquare {C : Type uC} [Category.{vC} C]
    (L P Q : C ⥤ C) (i : L ⋙ P ≅ Q) {A B T : C}
    (eta b : A ⟶ L.obj B) (e : A ⟶ A) (c : B ⟶ T) (d : T ⟶ T)
    (h : eta ≫ L.map (c ≫ d) = e ≫ b ≫ L.map c) :
    P.map eta ≫ (P.map (L.map c) ≫ i.hom.app T) ≫ Q.map d =
      P.map e ≫ P.map b ≫ (P.map (L.map c) ≫ i.hom.app T) := by
  have hNat := i.hom.naturality d
  change P.map (L.map d) ≫ i.hom.app T = i.hom.app T ≫ Q.map d at hNat
  calc
    _ = P.map eta ≫ P.map (L.map c) ≫ (i.hom.app T ≫ Q.map d) := by simp only [Category.assoc]
    _ = P.map eta ≫ P.map (L.map c) ≫ (P.map (L.map d) ≫ i.hom.app T) :=
      congrArg (fun h => P.map eta ≫ P.map (L.map c) ≫ h) hNat.symm
    _ = P.map (eta ≫ L.map (c ≫ d)) ≫ i.hom.app T := by
      simp only [Functor.map_comp, Category.assoc]
    _ = P.map (e ≫ b ≫ L.map c) ≫ i.hom.app T :=
      congrArg (fun h => P.map h ≫ i.hom.app T) h
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

/-- Every original lambda prefix keeps the full source and target ell maps before sequential iteration. -/
theorem correctedPrefix_evaluation (X : Carrier.{u, v}) (n m : ℕ) :
    (LoopPowerAtPoints.power n).map
        ((IterationMaps.level (m + n)).map (inputLambda.app X)) ≫
      (IterationMaps.prefixEvaluation n m).hom.app X ≫
        (LoopPowerAtPoints.power (n + 1)).map ((RightShift.bare X).map (ell (n + 1) m).hom) =
    (LoopPowerAtPoints.power n).map ((RightShift.bare X).map (ell n m).hom) ≫
      (LoopPowerAtPoints.power n).map ((j.obj X).adjointStructureMap (m + n)) ≫
        (IterationMaps.prefixEvaluation n m).hom.app X := by
  let P := LoopPowerAtPoints.power.{u, v} n
  let Q := LoopPowerAtPoints.power.{u, v} (n + 1)
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let eta := (IterationMaps.level (m + n)).map (inputLambda.app X)
  let b := (j.obj X).adjointStructureMap (m + n)
  let e := (RightShift.bare X).map (ell n m).hom
  let c := (RightShift.bare X).map (lowerCast n m).inv
  let d := (RightShift.bare X).map (ell (n + 1) m).hom
  have hBare : (RightShift.bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom) = c ≫ d :=
    (RightShift.bare X).map_comp _ _
  have hOriginal := inputLambda_ell_successor X n m
  have hSeq := HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential.sequential_adjoint_eq
    (m + n) (j.obj X)
  have hPoint : eta ≫ PointedCGWH.loop.map (c ≫ d) = e ≫ b ≫ PointedCGWH.loop.map c :=
    (congrArg (fun g => eta ≫ PointedCGWH.loop.map g) hBare).symm.trans
      (hOriginal.trans (congrArg (fun b => e ≫ b ≫ PointedCGWH.loop.map c) hSeq))
  have h := mapPrefixSquare PointedCGWH.loop P Q (loopPrefix n).symm eta b e c d hPoint
  have hPrefix := prefixEvaluation_decomposition X n m
  have hLeft := congrArg (fun p => P.map eta ≫ p ≫ Q.map d) hPrefix
  have hRight := congrArg (fun p => P.map e ≫ P.map b ≫ p) hPrefix
  exact hLeft.trans (h.trans hRight.symm)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open FunctionSpectrum FunctionIteration OriginalRawIndexCorrection OriginalSequentialFunctionChart
open scoped MonoidalClosed
/-- The original orthogonal index category for loop prefix comparison. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original monoidal structure on orthogonal indices for loop prefix comparison. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indices for loop prefix comparison. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
attribute [local instance] MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

universe uK vK

private theorem equalityWord3 {K : Type uK} [Category.{vK} K] {A B C D : K}
    (p : A = B) (q : B = C) (r : C = D) (s : A = D) :
    eqToHom s = eqToHom p ≫ eqToHom q ≫ eqToHom r := by
  simp only [eqToHom_trans]

/-- Both complete original prefix maps agree after the genuine loop-count transports. -/
theorem prefixLoopComparison (X : Carrier.{u, v}) (n m : ℕ) :
    (IterationMaps.prefixEvaluation n m).hom.app X =
      (loopComparison n).inv.app
          (PointedCGWH.loop.obj (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n + 1)))) ≫
        (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetNatIso
          n m).hom.app
          (j.obj X) ≫
        (loopComparison (n + 1)).hom.app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))) := by
  let P := LoopPowerAtPoints.power.{u, v} n
  let Z := PointedCGWH.loop.obj (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n + 1)))
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let p := ((congrArg (fun H => H ⋙ P) (IterationMaps.stepEvaluation_eq (m + n))).trans
    ((congrArg (fun H => IterationMaps.level (m + n + 1) ⋙ H)
      (Functor.Iteration.iterate_succ_prefix PointedCGWH.loop n).symm).trans
      (congrArg (fun k => IterationMaps.level k ⋙ LoopPowerAtPoints.power (n + 1)) (Nat.add_assoc m n 1))))
  let p0 := Functor.congr_obj (loopPower_same n).symm Z
  let ps := Functor.congr_obj
    (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetFunctorEq
      n m) (j.obj X)
  let p1 := Functor.congr_obj (loopPower_same (n + 1)) T
  have h0 : (IterationMaps.prefixEvaluation n m).hom.app X = eqToHom (Functor.congr_obj p X) :=
    eqToHom_app p X
  have hSource : (loopComparison n).inv.app Z = eqToHom p0 := eqToHom_app (loopPower_same n).symm Z
  have hSeq :
      (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetNatIso
        n m).hom.app
        (j.obj X) = eqToHom ps :=
    eqToHom_app
      (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetFunctorEq
        n m) (j.obj X)
  have hTarget : (loopComparison (n + 1)).hom.app T = eqToHom p1 := eqToHom_app (loopPower_same (n + 1)) T
  have hWord := equalityWord3 p0 ps p1 (Functor.congr_obj p X)
  have hRight := congrArg₂ (fun f g => f ≫ g) hSource
    (congrArg₂ (fun f g => f ≫ g) hSeq hTarget)
  exact h0.trans (hWord.trans hRight.symm)

/-- The whole original sequential prefix is carried to the same actual native prefix. -/
theorem prefixLoopComparison_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (loopComparison n).hom.app
        (PointedCGWH.loop.obj (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n + 1)))) ≫
      (IterationMaps.prefixEvaluation n m).hom.app X =
    (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetNatIso n m).hom.app
        (j.obj X) ≫
      (loopComparison (n + 1)).hom.app
        (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))) := by
  let Z := PointedCGWH.loop.obj (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n + 1)))
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let e := (loopComparison n).app Z
  let g :=
    (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetNatIso n m).hom.app
      (j.obj X) ≫ (loopComparison (n + 1)).hom.app T
  have h : (IterationMaps.prefixEvaluation n m).hom.app X = e.inv ≫ g := prefixLoopComparison X n m
  exact (congrArg (fun p => e.hom ≫ p) h).trans (Iso.hom_inv_id_assoc e g)

/-- The original complete sequential evaluation uses the same entire loop-count comparison. -/
theorem sequentialEvaluation_hom (X : Carrier.{u, v}) (n m : ℕ) :
    (sequentialEvaluation n m).hom.app X =
      (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X) ≫
        (loopComparison n).hom.app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))) := rfl

private theorem transportEvaluationSquare {K : Type uK} [Category.{vK} K]
    {A B C D E F G H : K} (u : A ⟶ B) (a : A ⟶ C) (a' : B ⟶ D)
    (b : C ⟶ E) (t : E ⟶ D) (i : C ⟶ F) (i' : E ⟶ G) (j' : D ⟶ H)
    (b' : F ⟶ G) (t' : G ⟶ H)
    (h0 : u ≫ a' = a ≫ b ≫ t) (h1 : b ≫ i' = i ≫ b') (h2 : t ≫ j' = i' ≫ t') :
    u ≫ (a' ≫ j') = (a ≫ i) ≫ b' ≫ t' := by
  calc
    _ = (u ≫ a') ≫ j' := (Category.assoc _ _ _).symm
    _ = (a ≫ b ≫ t) ≫ j' := congrArg (fun h => h ≫ j') h0
    _ = a ≫ b ≫ (t ≫ j') := by simp only [Category.assoc]
    _ = a ≫ b ≫ (i' ≫ t') := congrArg (fun h => a ≫ b ≫ h) h2
    _ = (a ≫ (b ≫ i')) ≫ t' := by simp only [Category.assoc]
    _ = (a ≫ (i ≫ b')) ≫ t' := congrArg (fun h => (a ≫ h) ≫ t') h1
    _ = _ := by simp only [Category.assoc]

/-- Every original sequential input unit retains the actual native pointed-prefix word after j. -/
theorem sequentialInput_evaluation (X : Carrier.{u, v}) (n m : ℕ) :
    PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m ≫
      (sequentialEvaluation (n + 1) m).hom.app X =
    (sequentialEvaluation n m).hom.app X ≫
      (LoopPowerAtPoints.power n).map ((j.obj X).adjointStructureMap (m + n)) ≫
        (IterationMaps.prefixEvaluation n m).hom.app X := by
  let u := PointedCGWH.SequentialSpectrum.levelMap
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m
  let b := (j.obj X).adjointStructureMap (m + n)
  let Z := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n))
  let L := PointedCGWH.loop.obj (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n + 1)))
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let a := (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso n m).hom.app (j.obj X)
  let a' := (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationEvaluationIso (n + 1) m).hom.app (j.obj X)
  let t :=
    (PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.evaluationPrefixTargetNatIso
      n m).hom.app
    (j.obj X)
  have h0 :=
    PointedCGWH.SequentialSpectrum.OrderedLoop.EvaluationAssociationGeometry.iterateUnit_evaluation_prefix_square n m
    (j.obj X)
  have h1 := (loopComparison n).hom.naturality b
  have h2 := (prefixLoopComparison_hom X n m).symm
  have h := transportEvaluationSquare u a a'
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map b) t
    ((loopComparison n).hom.app Z) ((loopComparison n).hom.app L) ((loopComparison (n + 1)).hom.app T)
    ((LoopPowerAtPoints.power n).map b) ((IterationMaps.prefixEvaluation n m).hom.app X) h0 h1 h2
  exact (congrArg (fun a' => u ≫ a') (sequentialEvaluation_hom X (n + 1) m)).trans
    (h.trans (congrArg (fun a => a ≫ (LoopPowerAtPoints.power n).map b ≫
      (IterationMaps.prefixEvaluation n m).hom.app X) (sequentialEvaluation_hom X n m).symm))

private theorem correctEvaluationSquare {K : Type uK} [Category.{vK} K]
    {A B C D E : K} (u : A ⟶ B) (a : A ⟶ C) (a' : B ⟶ D)
    (eta : C ⟶ E) (p : E ⟶ D) (e : C ⟶ C) (e' : D ⟶ D) (b : C ⟶ E)
    (h0 : u ≫ a' = a ≫ eta ≫ p) (h1 : eta ≫ p ≫ e' = e ≫ b ≫ p) :
    u ≫ (a' ≫ e') = (a ≫ e) ≫ b ≫ p := by
  calc
    _ = (u ≫ a') ≫ e' := (Category.assoc _ _ _).symm
    _ = (a ≫ eta ≫ p) ≫ e' := congrArg (fun h => h ≫ e') h0
    _ = a ≫ (eta ≫ p ≫ e') := by simp only [Category.assoc]
    _ = a ≫ (e ≫ b ≫ p) := congrArg (fun h => a ≫ h) h1
    _ = _ := by simp only [Category.assoc]

private theorem stageComparisonSquare {K : Type uK} [Category.{vK} K]
    {A B C D E F : K} (a : A ≅ C) (a' : B ≅ D) (b : E ≅ C) (b' : F ≅ D)
    (u : A ⟶ B) (v : E ⟶ F) (w : C ⟶ D)
    (hA : u ≫ a'.hom = a.hom ≫ w) (hB : v ≫ b'.hom = b.hom ≫ w) :
    u ≫ (a' ≪≫ b'.symm).hom = (a ≪≫ b.symm).hom ≫ v := by
  have hInv : w ≫ b'.inv = b.inv ≫ v := (CommSq.vert_inv (g := b) (h := b') ⟨hB⟩).w
  exact (Category.assoc u a'.hom b'.inv).symm.trans
    ((congrArg (fun h => h ≫ b'.inv) hA).trans
      ((Category.assoc a.hom w b'.inv).trans
        ((congrArg (fun h => a.hom ≫ h) hInv).trans (Category.assoc a.hom b.inv v).symm)))

/-- Both corrected original evaluations preserve the same complete original lambda transition. -/
theorem correctedEvaluation_input (X : Carrier.{u, v}) (n m : ℕ) :
    (IterationMaps.level m).map ((Functor.Iteration.inputTransition inputLambda n).app X) ≫
        (correctedEvaluation (n + 1) m).hom.app X =
      (correctedEvaluation n m).hom.app X ≫
        (LoopPowerAtPoints.power n).map ((j.obj X).adjointStructureMap (m + n)) ≫
          (IterationMaps.prefixEvaluation n m).hom.app X := by
  let u := (IterationMaps.level m).map ((Functor.Iteration.inputTransition inputLambda n).app X)
  let a := (IterationMaps.evaluationComparison n m).hom.app X
  let a' := (IterationMaps.evaluationComparison (n + 1) m).hom.app X
  let e := (LoopPowerAtPoints.power n).map ((RightShift.bare X).map (ell n m).hom)
  let e' := (LoopPowerAtPoints.power (n + 1)).map ((RightShift.bare X).map (ell (n + 1) m).hom)
  let b := (LoopPowerAtPoints.power n).map ((j.obj X).adjointStructureMap (m + n))
  let p := (IterationMaps.prefixEvaluation n m).hom.app X
  let eta := (LoopPowerAtPoints.power n).map ((IterationMaps.level (m + n)).map (inputLambda.app X))
  have h0 := inputTransition_evaluation inputLambda n m X
  have h1 := correctedPrefix_evaluation X n m
  exact correctEvaluationSquare u a a' eta p e e' b h0 h1

/-- Every original lambda input stage agrees with the same actual original sequential input stage. -/
theorem stagePointedNatIso_transition (X : Carrier.{u, v}) (n m : ℕ) :
    (IterationMaps.level m).map ((Functor.Iteration.inputTransition inputLambda n).app X) ≫
        (stagePointedNatIso (n + 1) m).hom.app X =
      (stagePointedNatIso n m).hom.app X ≫ PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m := by
  let A := (correctedEvaluation n m).app X
  let A' := (correctedEvaluation (n + 1) m).app X
  let B := (sequentialEvaluation n m).app X
  let B' := (sequentialEvaluation (n + 1) m).app X
  let u := (IterationMaps.level m).map ((Functor.Iteration.inputTransition inputLambda n).app X)
  let v := PointedCGWH.SequentialSpectrum.levelMap
    ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m
  let w := (LoopPowerAtPoints.power n).map ((j.obj X).adjointStructureMap (m + n)) ≫
    (IterationMaps.prefixEvaluation n m).hom.app X
  have hA : u ≫ A'.hom = A.hom ≫ w := correctedEvaluation_input X n m
  have hB : v ≫ B'.hom = B.hom ≫ w := sequentialInput_evaluation X n m
  exact stageComparisonSquare A A' B B' u v w hA hB

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open FunctionSpectrum FunctionIteration OriginalSequentialFunctionChart
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
attribute [local instance] MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual original native input diagram, followed by its unchanged original level. -/
def nativePointedDiagramFunctor (m : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ PointedCGWH.{u, v}) :=
  Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) inputLambda ⋙
    (Functor.whiskeringRight ℕ Carrier.{u, v} PointedCGWH.{u, v}).obj (IterationMaps.level m)

/-- The entire original sequential input diagram after the actual original j restriction. -/
def sequentialPointedDiagramFunctor (m : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ PointedCGWH.{u, v}) :=
  j ⋙ levelIterationDiagramFunctor m

/-- Every original native successor retains F^n(eta_X) at this actual level. -/
theorem nativePointedDiagramFunctor_succ (X : Carrier.{u, v}) (m n : ℕ) :
    ((nativePointedDiagramFunctor m).obj X).map (homOfLE (Nat.le_add_right n 1)) =
      (IterationMaps.level m).map ((Functor.Iteration.inputTransition inputLambda n).app X) :=
  congrArg (IterationMaps.level m).map (Functor.Iteration.inputDiagram_map_succ inputLambda X n)

/-- Every original sequential successor is the same actual original iterate-unit map. -/
theorem sequentialPointedDiagramFunctor_succ (X : Carrier.{u, v}) (m n : ℕ) :
    ((sequentialPointedDiagramFunctor m).obj X).map (homOfLE (Nat.le_add_right n 1)) =
      PointedCGWH.SequentialSpectrum.levelMap
        ((PointedCGWH.SequentialSpectrum.OrderedLoop.iterateUnit n).app (j.obj X)) m :=
  congrArg (PointedCGWH.SequentialSpectrum.evaluation m).map
    (PointedCGWH.SequentialSpectrum.OrderedLoop.iterationDiagram_map_succ (j.obj X) n)

/-- The complete original source calculation supplies every finite-index diagram square. -/
def pointedDiagramNatTrans (m : ℕ) : nativePointedDiagramFunctor.{u, v} m ⟶
    sequentialPointedDiagramFunctor m where
  app X := NatTrans.ofSequence (fun n => (stagePointedNatIso n m).hom.app X) (fun n => by
    have hNative := congrArg (fun f => f ≫ (stagePointedNatIso (n + 1) m).hom.app X)
      (nativePointedDiagramFunctor_succ X m n)
    have hSeq := congrArg (fun f => (stagePointedNatIso n m).hom.app X ≫ f)
      (sequentialPointedDiagramFunctor_succ X m n).symm
    exact hNative.trans ((stagePointedNatIso_transition X n m).trans hSeq))
  naturality _ _ f := by
    apply NatTrans.ext
    funext n
    exact (stagePointedNatIso n m).hom.naturality f

/-- Both actual original maps compare the entire native and sequential pointed input diagrams. -/
def pointedDiagramNatIso (m : ℕ) : nativePointedDiagramFunctor.{u, v} m ≅
    sequentialPointedDiagramFunctor m :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (F := (nativePointedDiagramFunctor m).obj X) (G := (sequentialPointedDiagramFunctor m).obj X)
      (fun n => (stagePointedNatIso n m).app X)
      (fun f => ((pointedDiagramNatTrans m).app X).naturality f))
    (fun f => (pointedDiagramNatTrans m).naturality f)

/-- Every forward stage uses both genuine native evaluation and original ell/sequence maps. -/
theorem pointedDiagramNatIso_hom_app (X : Carrier.{u, v}) (m n : ℕ) :
    ((pointedDiagramNatIso m).hom.app X).app n = (stagePointedNatIso n m).hom.app X := rfl

/-- Every inverse stage retains the opposite maps of that same complete original comparison. -/
theorem pointedDiagramNatIso_inv_app (X : Carrier.{u, v}) (m n : ℕ) :
    ((pointedDiagramNatIso m).inv.app X).app n = (stagePointedNatIso n m).inv.app X := rfl

/-- The whole literal original R/lambda input diagram is carried through its actual coefficient chart. -/
def lambdaInputDiagramNatIso :
    Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) lambdaStar ≅
      Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) inputLambda :=
  Functor.Iteration.inputDiagramNatIso (C := Carrier.{u, v}) functionIso lambdaStar

/-- Every original R/lambda stage and full input arrow remains at the original native level. -/
def lambdaPointedDiagramFunctor (m : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ PointedCGWH.{u, v}) :=
  Functor.Iteration.inputDiagramFunctor (C := Carrier.{u, v}) lambdaStar ⋙
    (Functor.whiskeringRight ℕ Carrier.{u, v} PointedCGWH.{u, v}).obj (IterationMaps.level m)

/-- Both actual lambda diagram maps compare with the same original sequential iteration. -/
def lambdaPointedDiagramNatIso (m : ℕ) : lambdaPointedDiagramFunctor.{u, v} m ≅
    sequentialPointedDiagramFunctor m :=
  Functor.isoWhiskerRight lambdaInputDiagramNatIso
    ((Functor.whiskeringRight ℕ Carrier.{u, v} PointedCGWH.{u, v}).obj (IterationMaps.level m)) ≪≫
      pointedDiagramNatIso m

/-- The raw groups retain the original lambda stages and the actual positive group functor. -/
def lambdaGroupDiagramFunctor (m k : ℕ) : Carrier.{u, v} ⥤ (ℕ ⥤ GrpCat.{v}) :=
  lambdaPointedDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (PointedCGWH.piNPositiveFunctor k)

/-- The complete original positive group diagram has both actual sequential input comparison maps. -/
def lambdaGroupDiagramNatIso (m k : ℕ) : lambdaGroupDiagramFunctor.{u, v} m k ≅
    j ⋙ groupIterationDiagramFunctor m k :=
  Functor.isoWhiskerRight (lambdaPointedDiagramNatIso m)
    ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (PointedCGWH.piNPositiveFunctor k)) ≪≫
      Functor.associator j (levelIterationDiagramFunctor m)
        ((Functor.whiskeringRight ℕ PointedCGWH.{u, v} GrpCat.{v}).obj (PointedCGWH.piNPositiveFunctor k))

/-- Every original lambda stage has the actual signed-diagonal group comparison and all its arrow squares. -/
def lambdaGroupDiagonalNatIso (m k : ℕ) : lambdaGroupDiagramFunctor.{u, v} m k ≅
    j ⋙ diagonalDiagramFunctor m k :=
  lambdaGroupDiagramNatIso m k ≪≫ Functor.isoWhiskerLeft j (iterationDiagonalNatIso m k)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open FunctionSpectrum FunctionIteration
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.IntegerColimitNormalization
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
attribute [local instance] MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The actual chosen raw Type colimit retains every original lambda input map and positive index. -/
def rawTypeColimitFunctor (m k : ℕ) : Carrier.{u, v} ⥤ Type v :=
  lambdaPointedDiagramFunctor m ⋙
    (Functor.whiskeringRight ℕ PointedCGWH.{u, v} (Type v)).obj (PointedCGWH.piNFunctor (k + 1)) ⋙ colim

/-- The actual filtered group quotient retains the same whole original lambda diagram. -/
def rawGroupColimitFunctor (m k : ℕ) : Carrier.{u, v} ⥤ GrpCat.{v} :=
  lambdaGroupDiagramFunctor m k ⋙ GrpCat.FilteredColimits.colimitFunctor

/-- Both genuine group quotient maps reach the original one signed integer functor. -/
def rawIntegerGroupNatIso (m k : ℕ) : rawGroupColimitFunctor.{u, v} m k ≅
    j ⋙ integerStablePiFunctor (integerDegree m k) :=
  Functor.isoWhiskerRight (lambdaGroupDiagonalNatIso m k) GrpCat.FilteredColimits.colimitFunctor ≪≫
    Functor.associator j (diagonalDiagramFunctor m k) GrpCat.FilteredColimits.colimitFunctor ≪≫
      Functor.isoWhiskerLeft j (integerColimitNatIso m k)

/-- The original source group/Type comparison gives both complete actual chosen quotient maps. -/
def rawTypeGroupColimitNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} m k ≅
    rawGroupColimitFunctor m k ⋙ forget GrpCat.{v} :=
  NatIso.ofComponents
    (fun X => GrpCat.FilteredColimits.sourceTypeColimitIso
      (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
      (LoopPowerAtPoints.positiveForgetComparison k) ((lambdaPointedDiagramFunctor m).obj X))
    (fun f => GrpCat.FilteredColimits.sourceTypeColimitIso_hom_naturality
      (PointedCGWH.piNPositiveFunctor k) (PointedCGWH.piNFunctor (k + 1))
      (LoopPowerAtPoints.positiveForgetComparison k) ((lambdaPointedDiagramFunctor m).map f))

/-- The actual raw positive Type quotient has both original signed integer comparison maps. -/
def rawIntegerTypeNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} m k ≅
    (j ⋙ integerStablePiFunctor (integerDegree m k)) ⋙ forget GrpCat.{v} :=
  rawTypeGroupColimitNatIso m k ≪≫ Functor.isoWhiskerRight (rawIntegerGroupNatIso m k) (forget GrpCat.{v})

/-- The original next-level predecessor has the literal signed integer degree k-m. -/
theorem predecessorIntegerDegree (m k : ℕ) : integerDegree (m + 1) k = (k : ℤ) - (m : ℤ) := by
  simp only [integerDegree, Nat.cast_add, Nat.cast_one]
  omega

/-- Both actual original predecessor quotient maps compare with the unchanged native integer functor. -/
def rawPredecessorTypeColimitNatIso (m k : ℕ) : rawTypeColimitFunctor.{u, v} (m + 1) k ≅
    OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ)) ⋙ forget GrpCat.{v} :=
  rawIntegerTypeNatIso (m + 1) k ≪≫
    eqToIso (congrArg (fun q => OrthogonalIntegerHomotopy.integerPiFunctor.{u, v} q ⋙ forget GrpCat.{v})
      (predecessorIntegerDegree m k))

/-- Every forward raw map retains the literal actual original predecessor quotient map. -/
theorem rawTypeColimitFunctor_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m k : ℕ) :
    (rawTypeColimitFunctor (m + 1) k).map f =
      OriginalFunctionTelescopePi.rawPiColimitMap f m k := rfl

/-- The full forward comparison retains the same original native input arrow. -/
theorem rawPredecessorTypeColimitNatIso_hom_naturality {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m k : ℕ) :
    OriginalFunctionTelescopePi.rawPiColimitMap f m k ≫
        (rawPredecessorTypeColimitNatIso m k).hom.app Y =
      (rawPredecessorTypeColimitNatIso m k).hom.app X ≫
        (forget GrpCat.{v}).map ((OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f) :=
  (rawPredecessorTypeColimitNatIso m k).hom.naturality f

/-- The complete inverse comparison retains the same original arrow and both opposite maps. -/
theorem rawPredecessorTypeColimitNatIso_inv_naturality {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m k : ℕ) :
    (forget GrpCat.{v}).map ((OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f) ≫
        (rawPredecessorTypeColimitNatIso m k).inv.app Y =
      (rawPredecessorTypeColimitNatIso m k).inv.app X ≫ OriginalFunctionTelescopePi.rawPiColimitMap f m k :=
  (rawPredecessorTypeColimitNatIso m k).inv.naturality f

/-- Original signed integer pi isomorphisms give every actual raw predecessor Type isomorphism. -/
theorem rawPiColimitMap_isIso_of_integer {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((OrthogonalIntegerHomotopy.integerPiFunctor q).map f))
    (m k : ℕ) : IsIso (OriginalFunctionTelescopePi.rawPiColimitMap f m k) := by
  let _ := hPi ((k : ℤ) - (m : ℤ))
  let g := (forget GrpCat.{v}).map
    ((OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))).map f)
  have hg : IsIso g := by infer_instance
  let e : ((OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))) ⋙
      forget GrpCat.{v}).obj X ≅ (rawTypeColimitFunctor (m + 1) k).obj X :=
    ((rawPredecessorTypeColimitNatIso m k).app X).symm
  let e' : ((OrthogonalIntegerHomotopy.integerPiFunctor ((k : ℤ) - (m : ℤ))) ⋙
      forget GrpCat.{v}).obj Y ≅ (rawTypeColimitFunctor (m + 1) k).obj Y :=
    ((rawPredecessorTypeColimitNatIso m k).app Y).symm
  have hSource : IsIso e.hom := e.isIso_hom
  have hComposite : IsIso (g ≫ e'.hom) := IsIso.comp_isIso' hg e'.isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ e.hom
    (OriginalFunctionTelescopePi.rawPiColimitMap f m k) (g ≫ e'.hom) hSource hComposite
    (rawPredecessorTypeColimitNatIso_inv_naturality f m k).symm

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration

open HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open FunctionIteration
open scoped CGWH.modelCategory MonoidalClosed
attribute [local instance] MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- All original signed integer maps detect the level class of the SAME actual R/lambda telescope. -/
theorem originalLambdaTelescopeMap_weak_of_integer {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map f)) :
    weakEquivalences Carrier.{u, v} (OriginalFunctionOmegaTelescope.telescopeFunctor.map f) :=
  HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison.telescopeMap_weak_of_raw_colimit_isIso
    HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison.orthogonalIndex
    lambdaStar OriginalFunctionTelescopePi.stepEvaluation
    HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison.orthogonalIndex_surjective
    f (fun m k => rawPiColimitMap_isIso_of_integer f hPi m k)

/-- The actual Carrier Homs use the same original lambda telescope and original Omega-target weak unit. -/
theorem originalLambdaPrecomp_bijective {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map f))
    (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    Function.Bijective (fun g : (toHomotopyCategory Carrier.{u, v}).obj Y ⟶
      (toHomotopyCategory Carrier.{u, v}).obj E => (toHomotopyCategory Carrier.{u, v}).map f ≫ g) := by
  let hF : ∀ ⦃A D : Carrier.{u, v}⦄ (g : A ⟶ D),
      weakEquivalences Carrier.{u, v} g →
        weakEquivalences Carrier.{u, v} (stabilizationFunction.map g) :=
    fun {A D} g hg => OriginalFunctionOmegaTelescope.originalFunction_preservesWeak (X := A) (Y := D) g hg
  exact PointedCGWH.Spectra.OriginalTelescopeOmegaHomRetract.originalPrecomp_bijective
    (I := OrthogonalOperatorIndex.{u, v}) (F := stabilizationFunction.{u, v})
    lambdaStar hF f (originalLambdaTelescopeMap_weak_of_integer f hPi) E
    (OriginalFunctionOmegaTelescope.originalLambda_weak E hE)

/-- Every original integer-pi isomorphism passes ALL original orthogonal Omega-target Hom tests. -/
theorem integerIsos_imply_omegaTests {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hPi : ∀ q : ℤ, IsIso ((Actual.OrthogonalIntegerHomotopy.integerPiFunctor q).map f)) :
    NativeK.omegaTests Actual.orthogonalFamily f :=
  fun E hE => originalLambdaPrecomp_bijective f hPi E hE

/-- The unrestricted original orthogonal signed-pi criterion implies the actual original all-target tests. -/
theorem integerPiStar_implies_omegaTests {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : Actual.OrthogonalIntegerHomotopy.integerPiStarEquivalences f) :
    NativeK.omegaTests Actual.orthogonalFamily f :=
  integerIsos_imply_omegaTests f ((Actual.OrthogonalIntegerHomotopy.integerPiStarEquivalences_iff f).mp hf)

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionRawIteration
