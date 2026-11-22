/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OmegaUnit

/-!
# The actual function-lambda telescope on orthogonal Omega targets

The original full function comparison proves level weak preservation. The actual
source lambda is weak on every original Omega target. Its chosen input-lambda
telescope has a weak stage-zero unit there, so the same target telescope is Omega.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionOmegaTelescope

open FunctionIteration FunctionSpectrum
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original whole function preserves the selected original level weak class. -/
theorem originalFunction_preservesWeak {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    weakEquivalences Carrier.{u, v} (stabilizationFunction.map f) := by
  let W := weakEquivalences Carrier.{u, v}
  have hMap := OmegaUnit.shiftedLoop_preserves_weak f hf
  apply W.of_postcomp (stabilizationFunction.map f)
    (stabilizationFunctionIso.hom.app Y) (W.of_isIso _)
  rw [stabilizationFunctionIso.hom.naturality f]
  exact W.comp_mem _ _ (W.of_isIso _) hMap

/-- The literal original lambda is level weak at an original Omega target. -/
theorem originalLambda_weak (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    weakEquivalences Carrier.{u, v}
      ((show 𝟭 Carrier.{u, v} ⟶ stabilizationFunction.{u, v} from lambdaStar).app E) := by
  let W := weakEquivalences Carrier.{u, v}
  let eta : 𝟭 Carrier.{u, v} ⟶ stabilizationFunction.{u, v} := lambdaStar
  let e : stabilizationFunction.{u, v} ≅ Delooping.firstDeloopingLoop.{u, v} :=
    stabilizationFunctionIso
  have hEta : eta ≫ e.hom = Delooping.delta := lambdaStar_stabilizationFunctionIso
  apply W.of_postcomp (eta.app E) (e.hom.app E) (W.of_isIso _)
  rw [← NatTrans.comp_app eta e.hom E, hEta]
  exact Delooping.delta_weak E hE

/-- The actual interval telescope is formed from the original function and original lambda. -/
abbrev telescopeFunctor : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedCoaugmentationTelescope.telescopeFunctor lambdaStar

/-- Its actual coaugmentation is the original chosen stage-zero leg. -/
abbrev unit : 𝟭 Carrier.{u, v} ⟶ telescopeFunctor :=
  EnrichedCoaugmentationTelescope.unit lambdaStar

/-- Every actual input transition retains the original weak lambda at this same Omega target. -/
theorem inputTransition_weak (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E)
    (n : ℕ) : weakEquivalences Carrier.{u, v}
      ((Functor.Iteration.inputTransition lambdaStar n).app E) :=
  EnrichedCoaugmentationTelescope.inputTransition_mem_weak
    (F := stabilizationFunction.{u, v}) lambdaStar
    (fun g hg => originalFunction_preservesWeak g hg) E (originalLambda_weak E hE) n

/-- The original function telescope unit is level weak at an original Omega target. -/
theorem unit_weak (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    weakEquivalences Carrier.{u, v} (unit.app E) :=
  EnrichedCoaugmentationTelescope.unit_mem_weak_of_preserves
    (F := stabilizationFunction.{u, v}) lambdaStar
    (fun g hg => originalFunction_preservesWeak g hg) E (originalLambda_weak E hE)

/-- Original K locality transfers across that actual weak unit at the Omega target. -/
theorem telescope_isOmega (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    Actual.OrthogonalIsOmega (telescopeFunctor.obj E) :=
  (NativeK.originalOmega_iff_of_levelWeak Actual.orthogonalFamily (unit.app E)
    (unit_weak E hE)).mp hE

omit B in
/-- Every full native target map keeps the actual original telescope unit square. -/
theorem unit_naturality {E E' : Carrier.{u, v}} (f : E ⟶ E') :
    f ≫ unit.app E' = unit.app E ≫ telescopeFunctor.map f := unit.naturality f

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionOmegaTelescope
