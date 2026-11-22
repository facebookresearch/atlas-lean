/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialIndexStabilizationArrowTransport
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalNativeRawSourceLabels
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialIndexSourceBridge

/-!
# Sequential charts for orthogonal function stabilization

Compares the orthogonal stabilization function with the shifted one-sphere loop through the representation-sphere coefficient isomorphism. The source coaugmentation is evaluated at every native degree, with explicit successor permutations and associativity casts matching the sequential adjoint.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat
open CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal.FunctionSpectrum
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart

open FunctionIteration
attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- Both actual scalar maps use the original j circle-to-representation coefficient Iso. -/
def scalarIso : cotensor (I := OrthogonalOperatorIndex.{u, v})
    (PointedCGWH.orthogonalSphere.{u, v} 1) ≅ cotensor PointedCGWH.sphereOne.{u, v} :=
  (ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v})
    (A := OrthogonalOperatorIndex.{u, v})).mapIso sequentialOrthogonalCoefficientIso.op

/-- The original scalar source map remains the actual precomposition at every native value. -/
theorem scalarIso_component (X : Carrier.{u, v}) (n : OrthogonalOperatorIndex.{u, v}) :
    component (scalarIso.hom.app X) n =
      (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app
        (X.toEnrichedFunctor.obj n) :=
  cotensorScalarMap_component _ X n

/-- An additional full chart retains the original free function and actual j coefficient. -/
def functionIso : stabilizationFunction.{u, v} ≅ IterationMaps.shiftedLoop.{u, v} :=
  nativeFreeFunctionNatIso 1 (PointedCGWH.orthogonalSphere.{u, v} 1) ≪≫
    Functor.isoWhiskerLeft Delooping.firstDelooping scalarIso

/-- The original lambda is carried through that same genuine full function chart. -/
def inputLambda : 𝟭 Carrier.{u, v} ⟶ IterationMaps.shiftedLoop.{u, v} :=
  lambdaStar ≫ functionIso.hom

/-- Its complete source word uses the actual original source adjoint before scalar transport. -/
theorem inputLambda_word : inputLambda.{u, v} =
    Delooping.comparisonNat 1 ≫
      (Functor.isoWhiskerLeft Delooping.firstDelooping scalarIso).hom := by
  let e₀ : stabilizationFunction.{u, v} ≅
      shiftedCotensor.{u, v} 1 (PointedCGWH.orthogonalSphere.{u, v} 1) :=
    nativeFreeFunctionNatIso.{u, v} 1 (PointedCGWH.orthogonalSphere.{u, v} 1)
  let e₁ : shiftedCotensor.{u, v} 1 (PointedCGWH.orthogonalSphere.{u, v} 1) ≅
      IterationMaps.shiftedLoop.{u, v} :=
    Functor.isoWhiskerLeft Delooping.firstDelooping.{u, v} scalarIso.{u, v}
  have hIso : functionIso.{u, v} = e₀ ≪≫ e₁ := rfl
  have h₀ : lambdaStar.{v, u} ≫ e₀.hom = Delooping.comparisonNat.{u, v} 1 :=
    lambdaStar_freeOutput.trans nativeSourceLambdaStar_output_nat
  change lambdaStar.{v, u} ≫ functionIso.{u, v}.hom = _
  rw [hIso, Iso.trans_hom, ← Category.assoc, h₀]
  rfl

/-- Every original native coefficient keeps the real nu label and the actual j sphere map. -/
theorem inputLambda_component (X : Carrier.{u, v}) (n : OrthogonalIndex) :
    component (inputLambda.app X) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      ShiftOmega.omegaMap X n 1 ≫
        (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))) := by
  rw [inputLambda_word]
  change component (Delooping.comparison 1 X ≫
    scalarIso.hom.app (Delooping.firstDelooping.obj X)) _ = _
  let g := scalarIso.hom.app (Delooping.firstDelooping.obj X)
  have hComp := component_comp (Delooping.comparison 1 X) g
    (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  have hSource := Delooping.comparison_component 1 X n
  have hScalar := scalarIso_component (Delooping.firstDelooping.obj X)
    (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  exact hComp.trans
    ((congrArg (fun f => f ≫ component g (OrthogonalOperatorIndex.ofIndex.{u, v} n))
      hSource).trans
      (congrArg (fun f => ShiftOmega.omegaMap X n 1 ≫ f) hScalar))

/-- The original function has both next-level loop maps through the same coefficient chart. -/
def stepEvaluation (m : ℕ) :
    stabilizationFunction.{u, v} ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + 1) ⋙ PointedCGWH.loop :=
  Functor.isoWhiskerRight functionIso (IterationMaps.level m) ≪≫
    IterationMaps.stepEvaluation m

/-- The actual one-step source equation retains the whole original lambda and native nu. -/
theorem lambda_stepEvaluation (X : Carrier.{u, v}) (m : ℕ) :
    (IterationMaps.level m).map (lambdaStar.app X) ≫ (stepEvaluation m).hom.app X =
      ShiftOmega.omegaMap X m 1 ≫
        (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1))) := by
  change (IterationMaps.level m).map (lambdaStar.app X) ≫
    ((IterationMaps.level m).map (functionIso.hom.app X) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  have h := inputLambda_component X m
  change (IterationMaps.level m).map (lambdaStar.app X ≫ functionIso.hom.app X) = _ at h
  exact ((IterationMaps.level m).map_comp _ _).symm.trans h

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart

open FunctionSpectrum OriginalNativeIndexSourceAction OriginalRawIndexCorrection
open OriginalSequentialIndexSourceBridge
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential
open CategoryTheory.Spectra.SpectrumIndexMaps
/-- The original orthogonal index category for the sequential function-spectrum chart. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original monoidal structure on orthogonal indices for the sequential function-spectrum chart. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indices for the sequential function-spectrum chart. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original symmetry on orthogonal indices for the sequential function-spectrum chart. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The whole actual j successor transpose is original lambda followed by its genuine index map. -/
theorem sequentialAdjoint_inputLambda (X : FunctionIteration.Carrier.{u, v}) (n : ℕ) :
    sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) n =
      component (inputLambda.app X) (OrthogonalOperatorIndex.ofIndex.{u, v} n) ≫
        PointedCGWH.loop.map ((RightShift.bare X).map (bareSuccessorPermutation n).hom) := by
  let A := PointedCGWH.orthogonalSphere.{u, v} 1
  let Z := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))
  let t := (RightShift.bare X).map (bareSuccessorPermutation n).hom
  let c := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app Z
  let w := ShiftOmega.omegaMap X n 1
  have hNative := sequentialOrthogonal_adjoint X n
  have hValue := successorOrthogonalIndexIso_hom_value X n
  have hFormula : sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) n =
      w ≫ (ihom A).map t ≫ c :=
    hNative.trans (congrArg (fun t => w ≫ (ihom A).map t ≫ c) hValue)
  have hPre : (ihom A).map t ≫ c = c ≫ PointedCGWH.loop.map t :=
    (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).naturality t
  have hAssoc : w ≫ c ≫ PointedCGWH.loop.map t =
      (w ≫ c) ≫ PointedCGWH.loop.map t := (Category.assoc _ _ _).symm
  have hInput := congrArg (fun h => h ≫ PointedCGWH.loop.map t) (inputLambda_component X n).symm
  exact hFormula.trans ((congrArg (fun h => w ≫ h) hPre).trans (hAssoc.trans hInput))

/-- The actual sequential successor has the complete original coefficient-first isometry label. -/
theorem sequentialAdjoint_label (X : FunctionIteration.Carrier.{u, v}) (n : ℕ) :
    sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) n =
      RightShift.adjoint X n (n + 1) 1 (eqToHom (Nat.add_comm 1 n)) ≫
        (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))) := by
  let A := PointedCGWH.orthogonalSphere.{u, v} 1
  let Z := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))
  let t := (RightShift.bare X).map (bareSuccessorPermutation n).hom
  let c := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app Z
  let w := ShiftOmega.omegaMap X n 1
  have hNative := sequentialOrthogonal_adjoint X n
  have hValue := successorOrthogonalIndexIso_hom_value X n
  have hFormula : sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) n =
      w ≫ (ihom A).map t ≫ c :=
    hNative.trans (congrArg (fun t => w ≫ (ihom A).map t ≫ c) hValue)
  have hTarget := (congrArg (fun h => h ≫ (ihom A).map t)
    (ShiftOmega.omegaMap_eq_adjoint X n 1)).trans
      (adjoint_target X n (n + 1) (n + 1) 1 (β_ (1 : OrthogonalIndex) n).hom
        (bareSuccessorPermutation n).hom)
  have hLabel := congrArg (RightShift.adjoint X n (n + 1) 1) (bareSuccessorPermutation_label n)
  exact hFormula.trans ((Category.assoc w ((ihom A).map t) c).symm.trans
    (congrArg (fun h => h ≫ c) (hTarget.trans hLabel)))

/-- Both original level casts compose with the actual coefficient-first degree map. -/
theorem successorCast_label (n m : ℕ) :
    eqToHom (Nat.add_comm 1 (m + n)) ≫ (lowerCast n m).inv = (upperCast n m).hom := by
  change eqToHom (Nat.add_comm 1 (m + n)) ≫ eqToHom (Nat.add_assoc m n 1) =
    eqToHom ((Nat.add_comm 1 (m + n)).trans (Nat.add_assoc m n 1))
  exact eqToHom_trans _ _

/-- The entire actual j successor transpose retains the original next-level arithmetic cast. -/
theorem sequentialAdjoint_sourceCast (X : FunctionIteration.Carrier.{u, v}) (n m : ℕ) :
    sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) (m + n) ≫
        PointedCGWH.loop.map ((RightShift.bare X).map (lowerCast n m).inv) =
      RightShift.adjoint X (m + n) (m + (n + 1)) 1 (upperCast n m).hom ≫
        (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))) := by
  let A := PointedCGWH.orthogonalSphere.{u, v} 1
  let Z := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} ((m + n) + 1))
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let g := (RightShift.bare X).map (lowerCast n m).inv
  let cZ := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app Z
  let cT := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app T
  let a := RightShift.adjoint X (m + n) ((m + n) + 1) 1 (eqToHom (Nat.add_comm 1 (m + n)))
  have hFirst := congrArg (fun h => h ≫ PointedCGWH.loop.map g) (sequentialAdjoint_label X (m + n))
  have hPre := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).naturality g
  have hTarget := adjoint_target X (m + n) ((m + n) + 1) (m + (n + 1)) 1
    (eqToHom (Nat.add_comm 1 (m + n))) (lowerCast n m).inv
  have hLabel := congrArg (RightShift.adjoint X (m + n) (m + (n + 1)) 1) (successorCast_label n m)
  exact hFirst.trans ((Category.assoc a cZ (PointedCGWH.loop.map g)).trans
    ((congrArg (fun h => a ≫ h) hPre.symm).trans
      ((Category.assoc a ((ihom A).map g) cT).symm.trans
        (congrArg (fun h => h ≫ cT) (hTarget.trans hLabel)))))

/-- The genuine original lambda and ell have the exact actual j successor square in every degree. -/
theorem inputLambda_ell_successor (X : FunctionIteration.Carrier.{u, v}) (n m : ℕ) :
    component (inputLambda.app X) (OrthogonalOperatorIndex.ofIndex.{u, v} (m + n)) ≫
        PointedCGWH.loop.map ((RightShift.bare X).map
          ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)) =
      (RightShift.bare X).map (ell n m).hom ≫
        sequentialAdjoint ((restriction sequentialOrthogonalOperatorIndexFunctor).obj X) (m + n) ≫
          PointedCGWH.loop.map ((RightShift.bare X).map (lowerCast n m).inv) := by
  let A := PointedCGWH.orthogonalSphere.{u, v} 1
  let Z := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} ((m + n) + 1))
  let T := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (m + (n + 1)))
  let g := (RightShift.bare X).map ((lowerCast n m).inv ≫ (ell (n + 1) m).hom)
  let cZ := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app Z
  let cT := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).app T
  let w := ShiftOmega.omegaMap X (m + n) 1
  let e := (RightShift.bare X).map (ell n m).hom
  let a := RightShift.adjoint X (m + n) (m + (n + 1)) 1 (upperCast n m).hom
  have hInput := congrArg (fun h => h ≫ PointedCGWH.loop.map g) (inputLambda_component X (m + n))
  have hPre := (MonoidalClosed.pre sequentialOrthogonalCoefficientIso.hom).naturality g
  have hEll := ell_step_adjoint X n m
  have hSeq := sequentialAdjoint_sourceCast X n m
  exact hInput.trans ((Category.assoc w cZ (PointedCGWH.loop.map g)).trans
    ((congrArg (fun h => w ≫ h) hPre.symm).trans
      ((Category.assoc w ((ihom A).map g) cT).symm.trans
        ((congrArg (fun h => h ≫ cT) hEll).trans
          ((Category.assoc e a cT).trans (congrArg (fun h => e ≫ h) hSeq.symm))))))

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalSequentialFunctionChart
