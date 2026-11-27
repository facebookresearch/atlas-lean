/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
public import MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels
public import Mathlib.Topology.Compactness.SigmaCompact
public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedProperImageOfFiniteAmplitude
public import MathlibExt.AlgebraicGeometry.EnhancedConvolutionSourceRequestsActualBoundedInverseImageSource

/-!
# Source proofs for the actual enhanced real convolution

The source's good-space hypotheses retain Hausdorffness, local
compactness, countability at infinity and finite flabby dimension.
The latter uses actual native bounded flabby resolutions. Every
descent/adjoint request concerns the already computed real graph
formula and its original enhanced localization, on every map.
Holonomic reconstruction and MHM admissibility are not conclusions
of these structural requests.

Source: D'Agnolo--Kashiwara1311.2374v2, Section2 conventions,
Sections3.3--3.4 and4.1--4.4, especially Proposition4.1.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
open MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
open MathlibExt.AlgebraicGeometry.IndSheafInverseImageModels
open MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
open MathlibExt.AlgebraicGeometry.BoundedIndImageModels
open MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
open MathlibExt.AlgebraicGeometry.BorderedIndDerivedModels
open MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
open MathlibExt.AlgebraicGeometry.BorderedGraphKernelModels
open MathlibExt.AlgebraicGeometry.BorderedRealTimeModels
open MathlibExt.AlgebraicGeometry.BoundedIndOperationSources
open MathlibExt.AlgebraicGeometry.EnhancedConvolutionModels
open MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels

attribute [local instance] requestAbelianPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- Graph properness of the computed finite real sum over the actual Hausdorff base. -/
theorem_wanted actual_time_sum_graph_source (M : TopCat.{0}) [T2Space M] : TimeSumGraphSource M

variable (k : Type) [Field k] (M : TopCat.{0}) [T2Space M]
  [CompactSheafSource k M]
  [CompactSheafSource k (enhancedSpace M).ambient]
  [CompactSheafSource k (boundarySpace (enhancedSpace M))]
  [CompactSheafSource k (doubleTimeSpace M).ambient]
  [CompactSheafSource k (sumProduct M)]
  [HasSheafify (Opens.grothendieckTopology (doubleTimeSpace M).ambient) (ModuleCat.{0} k)]
  [HasSheafify (Opens.grothendieckTopology (sumProduct M)) (ModuleCat.{0} k)]
  (B : ProperSource k (boundaryInclusion (enhancedSpace M)))
  (P : InverseSource k (baseProjection M))
  (G : TimeSumGraphSource M)
  [HasSheafify (Opens.grothendieckTopology
    (closedGraphSpace (doubleTimeSpace M) (enhancedSpace M) (timeSumBordered M G))) (ModuleCat.{0} k)]
  (S : TensorSource k (sumProduct M))
  (I : InverseSource k (firstProjection (doubleTimeSpace M) (enhancedSpace M)))
  (Q : ProperSource k (secondProjection (doubleTimeSpace M) (enhancedSpace M)))
  (T : TensorSource k (doubleTimeSpace M).ambient)
  (I₁ : InverseSource k (timeFirst M)) (I₂ : InverseSource k (timeSecond M))

/-- The actual real graph formula descends through every enhanced weak map in both inputs on a source good space. -/
theorem_wanted actual_enhanced_convolution_descent [LocallyCompactSpace M] [SigmaCompactSpace M]
    (h : FiniteFlabbyDimension k M) : ConvolutionDescentSource k M B P G S I Q T I₁ I₂

/-- Its original native localization admits the source convolution/internal-Hom adjunction on every enhanced object. -/
theorem_wanted actual_enhanced_convolution_closed [LocallyCompactSpace M] [SigmaCompactSpace M]
    (h : FiniteFlabbyDimension k M) (H : ConvolutionDescentSource k M B P G S I Q T I₁ I₂) :
    ConvolutionClosedSource k M B P G S I Q T I₁ I₂ H

end WantedExt.AlgebraicGeometry.EnhancedConvolutionSourceRequests
