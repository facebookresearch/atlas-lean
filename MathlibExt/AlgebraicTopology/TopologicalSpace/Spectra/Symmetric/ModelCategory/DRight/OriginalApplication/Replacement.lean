/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.DRight.OriginalApplication.WholeFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Zero
import MathlibExt.CategoryTheory.Limits.Shapes.ZeroObjectArrowFunctors

/-!
# Genuine source zero Arrow functors and SAME original-data replacements on D_R

The actual full D_R source carrier has a genuine native zero diagram.
Original OLD-J module-derived I/J data are applied to the full source initial
and terminal Arrow functors. All original middle objects and maps are retained.
The original map and factor statements retain `_B` to quantify over every caller
bottom of the given κ algorithm. The canonical implementation uses the
unique original bottom, and the whole-record readbacks identify it at every `_B`.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalReplacement

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction

/-- The genuine zero object on the original full D_R source index. -/
abbrev zero : SourceCarrier.{u, v} :=
  Native.Diagrams.zeroDiagram (A := PointedCGWH.SymmetricDRight.Index)

/-- The actual original source zero is simultaneously initial and terminal. -/
theorem zero_isZero : IsZero zero.{u, v} := Native.Diagrams.zeroDiagram_isZero

/-- The full source initial Arrow functor includes every original source map. -/
abbrev fromZeroArrow : SourceCarrier.{u, v} ⥤ Arrow SourceCarrier.{u, v} :=
  originalInitialArrowFunctor zero_isZero

/-- The full source terminal Arrow functor includes every original source map. -/
abbrev toZeroArrow : SourceCarrier.{u, v} ⥤ Arrow SourceCarrier.{u, v} :=
  originalTerminalArrowFunctor zero_isZero

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original OLD-J-derived I algorithm constructs the actual source Q functor. -/
def cofibrantReplacement : SourceCarrier.{u, v} ⥤ SourceCarrier.{u, v} :=
  fromZeroArrow ⋙ originalCofibrantFactorizationData.Z

/-- The original OLD-J-derived J algorithm constructs the actual source R functor. -/
def fibrantReplacement : SourceCarrier.{u, v} ⥤ SourceCarrier.{u, v} :=
  toZeroArrow ⋙ originalFibrantFactorizationData.Z

/-- The exact original source π is the old I second factor at the full initial Arrow. -/
def cofibrantProjection : cofibrantReplacement.{u, v} ⟶ 𝟭 SourceCarrier.{u, v} :=
  Functor.whiskerLeft fromZeroArrow originalCofibrantFactorizationData.p

/-- The exact original source I first factor retains the same source zero endpoint. -/
def initialToCofibrantReplacement : (Functor.const SourceCarrier.{u, v}).obj zero ⟶
    cofibrantReplacement :=
  Functor.whiskerLeft fromZeroArrow originalCofibrantFactorizationData.i

/-- The exact original source ι is the old J first factor at the full terminal Arrow. -/
def fibrantUnit : 𝟭 SourceCarrier.{u, v} ⟶ fibrantReplacement.{u, v} :=
  Functor.whiskerLeft toZeroArrow originalFibrantFactorizationData.i

/-- The exact original source J second factor retains the same source zero endpoint. -/
def fibrantReplacementToZero : fibrantReplacement.{u, v} ⟶
    (Functor.const SourceCarrier.{u, v}).obj zero :=
  Functor.whiskerLeft toZeroArrow originalFibrantFactorizationData.p

omit B in
/-- Every original source Q map retains the complete OLD-J source I middle Arrow map. -/
theorem cofibrantReplacement_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y : SourceCarrier.{u, v}}
  (f : X ⟶ Y) :
    cofibrantReplacement.map f = originalCofibrantFactorizationData.Z.map (fromZeroArrow.map f) :=
  rfl

omit B in
/-- Every original source R map retains the complete OLD-J source J middle Arrow map. -/
theorem fibrantReplacement_map [_B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType] {X Y : SourceCarrier.{u, v}} (f
  : X ⟶ Y) :
    fibrantReplacement.map f = originalFibrantFactorizationData.Z.map (toZeroArrow.map f) := rfl

end PointedCGWH.Spectra.Symmetric.DRightPresentation.OriginalReplacement
