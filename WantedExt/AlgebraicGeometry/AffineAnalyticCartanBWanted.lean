/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.AnalyticRealization

/-!
# Cartan B on the actual analytification of a smooth affine scheme

The manifold and holomorphic sheaf live on the fixed complex-point topology,
and the regular-function map is normalized pointwise. Request that analytic
structure for smooth affine complex schemes in every dimension, and
the higher-cohomology vanishing of any finite-presentation holomorphic
module sheaf. The cohomology is the actual derived morphism group from the
holomorphic structure module; no supplied vanishing predicate is used.

Reference: H. Cartan, *Variétés analytiques complexes et cohomologie*,
Colloque sur les fonctions de plusieurs variables, Bruxelles (1953),
41–55, Théorème B; affine complex varieties are Stein.
https://en.wikipedia.org/wiki/Cartan%27s_theorems_A_and_B
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffineAnalyticCartanBWanted

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AnalyticRealization

attribute [local instance] HasDerivedCategory.standard

/-- Construct the normalized holomorphic realization on the actual smooth
affine complex-point space. Its two classes specify charts and evaluation. -/
public def_wanted smoothAffineAnalyticRealization
    (X : ComplexScheme) (d : ℕ)
    [IsAffine X.left] [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] :
    Σ a : AnalyticManifold X d, @RegularFunctions X d a

/-- Cartan B for the actual holomorphic coefficient sheaf on this affine
analytification, including modules that need not be algebraizations. -/
public theorem_wanted positive_cohomology_subsingleton
    (X : ComplexScheme) (d : ℕ)
    [IsAffine X.left] [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom]
    [AnalyticManifold X d] [RegularFunctions X d]
    (M : AnalyticModules X d) [SheafOfModules.IsFinitePresentation M]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton
      (((DerivedCategory.singleFunctor (AnalyticModules X d) 0).obj
          (SheafOfModules.unit (holomorphicRingSheaf X d))) ⟶
        ((DerivedCategory.singleFunctor (AnalyticModules X d) 0).obj M)
          ⟦(n : ℤ)⟧)

end WantedExt.AlgebraicGeometry.AffineAnalyticCartanBWanted
