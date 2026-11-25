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
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

/-!
# GAGA for bounded coherent hypercohomology

The objects and comparison are fixed in MathlibExt by the actual normalized
analytic module pullback. For a smooth proper complex scheme, ask for the
normalized analytic realization, the exactness of the analytic pullback, and
the bijectivity of the resulting comparison on bounded complexes with
finitely presented terms.

References: J.-P. Serre, *Géométrie algébrique et géométrie analytique*,
Ann. Inst. Fourier 6 (1956), 1–42, Théorème 1 (projective case),
https://doi.org/10.5802/aif.59; A. Grothendieck, SGA 1, Exposé XII,
Théorème 4.2 (proper case; Théorème 4.4 is the equivalence of categories). The bounded-complex statement follows from the
statement for coherent sheaves by induction on the length of the complex.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoherentHypercohomologyGAGAWanted

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.CoherentAnalyticHypercohomology

attribute [local instance] HasDerivedCategory.standard

/-- Construct the pointwise normalized analytic realization for a smooth proper
scheme; the carrier and holomorphic sheaf are fixed in MathlibExt. -/
public def_wanted smoothProperAnalyticRealization
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom] :
    Σ a : AnalyticManifold X d, @RegularFunctions X d a

/-- Exactness of the actual normalized analytic module pullback. -/
public def_wanted analyticPullback_preservesFiniteLimits
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    [AnalyticManifold X d] [RegularFunctions X d] :
    PreservesFiniteLimits (pullback X d)

/-- The fixed hypercohomology map is bijective for every bounded coherent
complex. Coherence is Mathlib finite presentation on the actual module sheaf. -/
public theorem_wanted comparison_bijective
    (X : ComplexScheme) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [IsProper X.hom]
    [AnalyticManifold X d] [RegularFunctions X d]
    [PreservesFiniteLimits (pullback X d)]
    (K : CochainComplex X.left.Modules ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i : ℤ, SheafOfModules.IsFinitePresentation (K.X i)] (n : ℤ) :
    Function.Bijective (comparison X d K n)

end WantedExt.AlgebraicGeometry.CoherentHypercohomologyGAGAWanted
