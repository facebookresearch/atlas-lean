/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.IterationMaps
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKLocalLifting
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHLoopWeakEquivalence

/-!
# The original native shifted-loop telescope on orthogonal Omega targets

The actual shifted-loop functor preserves the original level weak class.
Its input-delta telescope therefore has a level weak stage-zero unit on
every full orthogonal Omega target. Original K locality transfers across
that same weak unit, so the actual target telescope is Omega as well.
No Omega assertion about an arbitrary input telescope is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OmegaUnit

open IterationMaps FunctionSpectrum

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- A native level weak arrow retains the entire weak map at every original dimension. -/
theorem component_weak {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) (m : ℕ) :
    weakEquivalences PointedCGWH.{u, v} ((level m).map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq,
    EvaluationTransfer.evaluationProperty_iff] at hf
  exact hf (OrthogonalOperatorIndex.ofIndex.{u, v} m)

omit B in
/-- The actual scalar-loop image preserves the original selected weak class. -/
theorem loop_preserves_weak {A C : PointedCGWH.{u, v}} (f : A ⟶ C)
    (hf : weakEquivalences PointedCGWH.{u, v} f) :
    weakEquivalences PointedCGWH.{u, v} (PointedCGWH.loop.map f) := by
  have hRight : CGWH.weakHomotopyEquivalences f.right :=
    (HomotopicalAlgebra.weakEquivalence_iff f.right).mp
      ((PointedCGWH.weakEquivalence_iff f).mp
        ((HomotopicalAlgebra.weakEquivalence_iff f).mpr hf))
  have hLoop := PointedCGWH.loop_map_mem_weakHomotopyEquivalences f hRight
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    ((PointedCGWH.weakEquivalence_iff _).mpr
      ((HomotopicalAlgebra.weakEquivalence_iff _).mpr hLoop))

/-- Both original functor maps and the identity-component evaluation prove level preservation. -/
theorem shiftedLoop_preserves_weak {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences Carrier.{u, v} f) :
    weakEquivalences Carrier.{u, v} (shiftedLoop.map f) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq,
    EvaluationTransfer.evaluationProperty_iff]
  intro a
  rcases a with ⟨m⟩
  change weakEquivalences PointedCGWH.{u, v}
    (component (shiftedLoop.map f) (OrthogonalOperatorIndex.ofIndex.{u, v} m))
  have h := loop_preserves_weak ((level (m + 1)).map f) (component_weak f hf (m + 1))
  have hMap : component (shiftedLoop.map f) (OrthogonalOperatorIndex.ofIndex.{u, v} m) =
      PointedCGWH.loop.map (component f (OrthogonalOperatorIndex.ofIndex.{u, v} (m + 1))) :=
    (cotensorMap_component PointedCGWH.sphereOne _ _).trans
      (congrArg (ihom PointedCGWH.sphereOne).map
        (RightShift.shift_map_component 1 m f))
  rw [hMap]
  exact h

/-- The same actual full native input-delta diagram supplies the chosen interval telescope. -/
abbrev telescopeFunctor : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  EnrichedCoaugmentationTelescope.telescopeFunctor Delooping.delta

/-- Its actual stage-zero leg is the original native telescope coaugmentation. -/
abbrev unit : 𝟭 Carrier.{u, v} ⟶ telescopeFunctor :=
  EnrichedCoaugmentationTelescope.unit Delooping.delta

/-- Original delta weakness and genuine functor preservation imply weakness of every input step. -/
theorem inputTransition_weak (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E)
    (n : ℕ) : weakEquivalences Carrier.{u, v} ((inputTransition n).app E) :=
  EnrichedCoaugmentationTelescope.inputTransition_mem_weak Delooping.delta
    shiftedLoop_preserves_weak E (Delooping.delta_weak E hE) n

/-- The actual interval telescope unit is level weak at every full original Omega target. -/
theorem unit_weak (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    weakEquivalences Carrier.{u, v} (unit.app E) :=
  EnrichedCoaugmentationTelescope.unit_mem_weak_of_preserves Delooping.delta
    shiftedLoop_preserves_weak E (Delooping.delta_weak E hE)

/-- The original K tests transfer across that same unit to the actual target telescope. -/
theorem telescope_isOmega (E : Carrier.{u, v}) (hE : Actual.OrthogonalIsOmega E) :
    Actual.OrthogonalIsOmega (telescopeFunctor.obj E) :=
  (NativeK.originalOmega_iff_of_levelWeak Actual.orthogonalFamily (unit.app E)
    (unit_weak E hE)).mp hE

omit B in
/-- Every original target arrow retains the same actual native telescope unit square. -/
theorem unit_naturality {E E' : Carrier.{u, v}} (f : E ⟶ E') :
    f ≫ unit.app E' = unit.app E ≫ telescopeFunctor.map f := unit.naturality f

omit B in
/-- The unit keeps the exact original chosen stage-zero colimit leg. -/
theorem unit_eq_leg (E : Carrier.{u, v}) :
    unit.app E = EnrichedCoaugmentationTelescope.leg Delooping.delta E 0 := rfl

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OmegaUnit
