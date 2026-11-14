/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology
public import MathlibExt.AlgebraicGeometry.ProjectiveDirectImage

/-!
# GAGA for bounded coherent hypercohomology

The objects and comparison are fixed in MathlibExt by the actual normalized
analytic module pullback. For a smooth projective complex scheme, ask for
its exactness and for the resulting comparison on bounded complexes with
finite-presentation terms. The public curve comparisons for functions and
units provide partial nearby results; no dimension is excluded based on them.

Reference: J.-P. Serre, *Géométrie algébrique et géométrie analytique*,
Ann. Inst. Fourier 6 (1956), 1–42, Théorème 1 and its bounded-complex
hypercohomology consequence. https://doi.org/10.5802/aif.59
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoherentHypercohomologyGAGAWanted

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology
open MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
  (IsProjectiveOverC)

attribute [local instance] HasDerivedCategory.standard

/-- Construct the pointwise normalized analytic realization for a smooth
projective scheme; the carrier and holomorphic sheaf are fixed in MathlibExt. -/
public def_wanted smoothProjectiveAnalyticRealization
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    (hprojective : IsProjectiveOverC X) :
    Σ a : AnalyticManifold X d, @RegularFunctions X d a

/-- Exactness of the actual normalized analytic module pullback. -/
public def_wanted analyticPullback_preservesFiniteLimits
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    [AnalyticManifold X d] [RegularFunctions X d]
    (hprojective : IsProjectiveOverC X) :
    PreservesFiniteLimits (pullback X d)

/-- The fixed hypercohomology map is bijective for every bounded coherent
complex. Coherence is Mathlib finite presentation on the actual module sheaf. -/
public theorem_wanted comparison_bijective
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    [AnalyticManifold X d] [RegularFunctions X d]
    [PreservesFiniteLimits (pullback X d)]
    (hprojective : IsProjectiveOverC X)
    (K : CochainComplex X.left.Modules ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i : ℤ, SheafOfModules.IsFinitePresentation (K.X i)] (n : ℤ) :
    Function.Bijective (comparison X d K n)

end WantedExt.AlgebraicGeometry.CoherentHypercohomologyGAGAWanted
