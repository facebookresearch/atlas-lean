/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels

/-!
# Wanted native singular/de Rham and rational Chern comparisons

Every source operation uses the actual smooth simplex, native chain/dual
cochain map, fixed parameter integral, actual coefficient inclusion or
the fixed curvature determinant. The construction and comparison proofs
are independent of metric existence and nonabelian Hodge correspondence.
-/

open CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas
open MathlibExt.AlgebraicGeometry.ManifoldSingularCohomologyModels
open MathlibExt.AlgebraicGeometry.SmoothManifoldSingularModels
open MathlibExt.AlgebraicGeometry.RealDeRhamSingularModels
open MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]

/-- The native simplex affine maps preserve this exact smooth extension predicate. -/
theorem_wanted native_smooth_singular_source [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] :
  SmoothSingularSource (n := n) (M := M)

variable [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M] [SmoothSingularSource (n := n) (M := M)]

/-- The native closed/exact quotient agrees with native cochain homology on each actual closed form. -/
def_wanted native_even_deRham_quotient_source (q : ℕ) : EvenDeRhamQuotientSource (n := n) (M := M) q

/-- Native parameter integration defines the fixed all-degree singular cochain map. -/
def_wanted native_smooth_singular_integration : SingularIntegrationSource (n := n) (M := M)

/-- The genuine de Rham theorem concerns the same actual integration map. -/
theorem_wanted native_smooth_singular_integration_quasiIso [T2Space M] [SecondCountableTopology M]
    (I : SingularIntegrationSource (n := n) (M := M)) : QuasiIso I.map

/-- Smooth approximation compares the literal continuous-to-smooth dual cochain map. -/
theorem_wanted native_continuous_smooth_cochains_quasiIso [T2Space M] [SecondCountableTopology M]
    (R : Type) [CommRing R] : QuasiIso (continuousToSmoothCochains (n := n) (M := M) R)

/-- The actual coefficient inclusion acts on every native simplex generator. -/
def_wanted native_rational_singular_coefficient_source : RationalCoefficientSource (n := n) (M := M)

/-- This actual coefficient/smooth-restriction cohomology map is injective. -/
theorem_wanted native_rational_to_smooth_real_class_injective [T2Space M] [SecondCountableTopology M]
    (S : RationalCoefficientSource (n := n) (M := M)) (p : ℕ) :
  Function.Injective (rationalToSmoothRealClass S p).hom

/-- Construct the actual closed form with every prescribed curvature-determinant coefficient. -/
def_wanted native_connection_chernWeil_form {r : ℕ} (B : SmoothComplexBundle n M r)
    (C : SmoothConnection B) (q : ℕ) : ChernWeilFormSource B C q

/-- Chern--Weil connection independence concerns the actual classes of the same smooth bundle. -/
theorem_wanted native_chernWeil_class_independence {r : ℕ} (B : SmoothComplexBundle n M r)
    (C D : SmoothConnection B) (q : ℕ) (P : ChernWeilFormSource B C q)
    (Q : ChernWeilFormSource B D q) : chernWeilClass B P = chernWeilClass B Q

/-- The actual integrated curvature coefficient has its uniquely normalized rational Chern class. -/
def_wanted native_rational_chern_class [T2Space M] [SecondCountableTopology M]
    {r : ℕ} (B : SmoothComplexBundle n M r) (C : SmoothConnection B)
    (I : SingularIntegrationSource (n := n) (M := M))
    (S : RationalCoefficientSource (n := n) (M := M))
    (q : ℕ) (P : ChernWeilFormSource B C q) (Q : EvenDeRhamQuotientSource (n := n) (M := M) q) :
  RationalChernClassSource B C I S q P Q
