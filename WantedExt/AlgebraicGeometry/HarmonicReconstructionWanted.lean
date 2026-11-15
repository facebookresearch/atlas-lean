/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces

/-!
# Actual harmonic reconstruction and metric existence

Simpson, alg-geom/9604005v1, section 2 and Theorem 2.3. Every requested
connection and horizontal comparison is fixed by the native local formula.
Metric existence is requested from a compact Kähler manifold and a flat
connection whose actual horizontal sheaf is semisimple. The three
pluriharmonic equations are conclusions, together with metric positivity.
No harmonic metric, free holonomy map, or NAH equivalence is assumed.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HarmonicReconstructionWanted

open _root_.CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.HarmonicHorizontalSheaves
open MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
open scoped Manifold ContDiff Matrix Matrix.Norms.Elementwise

def_wanted adjoint_realization (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (r : ℕ) (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (A : SmoothConnection B) :
    ConnectionRealization B (adjointConnection B h A)

def_wanted higgs_metric_realization (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (r : ℕ) (B : SmoothComplexBundle n M r)
    (h : HermitianMetric B) (H : HolomorphicHiggsField B) :
    ConnectionRealization B (reconstructedConnection B h H.value)

def_wanted local_flat_frame (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (r : ℕ) (B : SmoothComplexBundle n M r)
    (A : SmoothConnection B) (_flat : IsFlat B A) (x : M) : LocalFlatFrame B A x

def_wanted local_horizontal_comparison (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (r : ℕ) (B : SmoothComplexBundle n M r)
    (A : SmoothConnection B) [SectionCalculus B A.value] (_flat : IsFlat B A)
    (x : M) (F : LocalFlatFrame B A x) : LocalHorizontalComparison B A x F

def_wanted pluriharmonic_metric (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M] [ConnectedSpace M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] (eta : KahlerStructure n M)
    (r : ℕ) (B : SmoothComplexBundle n M r) (A : SmoothConnection B)
    [SectionCalculus B A.value]
    [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
    (_flat : IsFlat B A) (_semisimple : SemisimpleHorizontals B A) :
    {h : HermitianMetric B // IsPluriharmonic B h A}

end WantedExt.AlgebraicGeometry.HarmonicReconstructionWanted
