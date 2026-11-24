/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HiggsSmoothRealizationModels

/-!
# The inverse Higgs/kernel comparison on the same smooth scalar extension

The O-linear comparison targets the actual harmonic bar kernel. It
preserves the actual theta maps, and its smooth scalar extension is
normalized against the same physical module realization. The connection
is the actual reconstructed connection in the holomorphic realization.
Metric existence and the comparison provider are separate Wanted goals.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HiggsKernelComparisonModels

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry HarmonicHorizontalSheaves
open HarmonicReconstructionInterfaces HarmonicHolomorphicModuleModels
open HolomorphicCotangentModuleModels HolomorphicSheafHiggsModels HolomorphicSmoothScalarModels
open HarmonicHolomorphicFrameModels HiggsSmoothRealizationModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  {T : TensorAssociatorSource (n := n) (M := M)} {W : CotangentWedgeSource (n := n) (M := M)}
  (S : HolomorphicSmoothInclusionSource (n := n) (M := M)) (E : HiggsModule T W)
  (R : HiggsRealization S E) (h : HermitianMetric R.physical.bundle)
  (C : ConnectionRealization R.physical.bundle (reconstructedConnection R.physical.bundle h R.geometry.value))
  [SectionCalculus R.physical.bundle (unitaryPart R.physical.bundle h C.connection)]
  [BarMultiplicationCalculus R.physical.bundle h C.connection]
  [KernelSheafCondition R.physical.bundle h C.connection]

/-- The actual inverse comparison preserves theta and the whole native smooth scalar-extension realization. -/
structure HiggsKernelComparison (H : HarmonicHiggsModel R.physical.bundle h C.connection) where
  kernelScalar : letI := R.physical.calculus; letI := R.physical.multiplication; letI := R.physical.gluing
    KernelSmoothExtensionSource R.physical.bundle h C.connection S
  iso : E.module ≅ holomorphicModule R.physical.bundle h C.connection
  theta : iso.hom ≫ H.theta = E.theta ≫ tensorMap iso.hom (𝟙 _)
  physical_normalized : letI := R.physical.calculus; letI := R.physical.multiplication; letI := R.physical.gluing
    (smoothScalarExtension S).map iso.hom ≫ kernelScalar.iso.hom = R.physical.comparison.hom

end MathlibExt.AlgebraicGeometry.HiggsKernelComparisonModels
