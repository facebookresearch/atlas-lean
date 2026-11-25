/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RealDeRhamSingularModels
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# All rational Chern classes with actual singular/de Rham normalization

Rational and real cochains are actual native linear duals of the smooth
singular chain complexes. Coefficient change is normalized on every actual
simplex. Its cohomology map is the native homology map and exact scalar
restriction comparison. The continuous-to-smooth comparison is the native
chain inclusion, not an independently chosen map.

Each rational Chern class lies in actual rational singular cohomology and
is fixed by the actual integrated Chern--Weil coefficient. Coefficient-map
injectivity is a separate source theorem; no Chern vanishing or harmonic
correspondence conclusion belongs to the construction data.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels

open CategoryTheory Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry ManifoldDifferentialForms
open HarmonicChernWeilFormulas ManifoldSingularCohomologyModels
open SmoothManifoldSingularModels RealDeRhamSingularModels
open scoped Manifold ContDiff Simplicial

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [SmoothSingularSource (n := n) (M := M)]

/-- The coefficient homomorphism is the actual rational inclusion into R. -/
def rationalRealMap : ℚ →+* ℝ := algebraMap ℚ ℝ

/-- The actual real cochains viewed as rational modules via the native scalar restriction. -/
def restrictedRealCochains : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  ((ModuleCat.restrictScalars rationalRealMap).mapHomologicalComplex (.up ℕ)).obj
    (smoothSingularCochains (n := n) (M := M) ℝ)

/-- The coefficient cochain map is fixed on every native simplex generator. -/
structure RationalCoefficientSource where
  map : smoothSingularCochains (n := n) (M := M) ℚ ⟶ restrictedRealCochains (n := n) (M := M)
  normalized : ∀ (p : ℕ) (α : (smoothSingularCochains (n := n) (M := M) ℚ).X p)
    (σ : (smoothSingularSet (n := n) (M := M)) _⦋p⦌),
      smoothCochainValue (n := n) ℝ p ((map.f p).hom α) σ =
        rationalRealMap (smoothCochainValue (n := n) ℚ p α σ)

/-- Scalar restriction commutes with this same native cochain homology by the native exact-functor comparison. -/
def restrictionHomologyIso (p : ℕ) :
    (restrictedRealCochains (n := n) (M := M)).homology p ≅
      (ModuleCat.restrictScalars rationalRealMap).obj
        ((smoothSingularCochains (n := n) (M := M) ℝ).homology p) :=
  ((smoothSingularCochains (n := n) (M := M) ℝ).sc p).mapHomologyIso
    (ModuleCat.restrictScalars rationalRealMap)

/-- The actual smooth coefficient-change map on native cochain cohomology. -/
def smoothRationalClassMap (S : RationalCoefficientSource (n := n) (M := M)) (p : ℕ) :
    (smoothSingularCochains (n := n) (M := M) ℚ).homology p ⟶
      (ModuleCat.restrictScalars rationalRealMap).obj
        ((smoothSingularCochains (n := n) (M := M) ℝ).homology p) :=
  HomologicalComplex.homologyMap S.map p ≫ (restrictionHomologyIso (n := n) (M := M) p).hom

/-- Actual continuous rational cohomology first restricts along the native smooth-chain inclusion. -/
def rationalToSmoothRealClass (S : RationalCoefficientSource (n := n) (M := M)) (p : ℕ) :
    rationalCohomology (TopCat.of M) p ⟶
      (ModuleCat.restrictScalars rationalRealMap).obj
        ((smoothSingularCochains (n := n) (M := M) ℝ).homology p) :=
  HomologicalComplex.homologyMap (continuousToSmoothCochains (n := n) (M := M) ℚ) p ≫
    smoothRationalClassMap S p

variable [ExteriorTheory ℝ (Coordinates n) M]
  {r : ℕ} (B : SmoothComplexBundle n M r) (C : SmoothConnection B)
  (I : SingularIntegrationSource (n := n) (M := M))
  (S : RationalCoefficientSource (n := n) (M := M))

/-- A positive rational Chern class is fixed by its actual native integrated Chern--Weil class. -/
structure RationalChernClassSource (q : ℕ) (P : ChernWeilFormSource B C q)
    (Q : EvenDeRhamQuotientSource (n := n) (M := M) q) where
  value : rationalCohomology (TopCat.of M) ((2 * q + 1) + 1)
  normalized : (rationalToSmoothRealClass S ((2 * q + 1) + 1)).hom value =
    (integratedEvenClass I q Q).hom (chernWeilClass B P)

/-- Every positive rational Chern class is tested in its actual singular-cohomology degree. -/
def AllRationalChernZero (P : ∀ q : ℕ, ChernWeilFormSource B C q)
    (Q : ∀ q : ℕ, EvenDeRhamQuotientSource (n := n) (M := M) q)
    (R : ∀ q : ℕ, RationalChernClassSource B C I S q (P q) (Q q)) : Prop :=
  ∀ q : ℕ, (R q).value = 0

/-- Native coefficient injectivity transfers zero of all actual real de Rham classes to all rational classes. -/
theorem allRationalChernZero_of_deRham
    (P : ∀ q : ℕ, ChernWeilFormSource B C q)
    (Q : ∀ q : ℕ, EvenDeRhamQuotientSource (n := n) (M := M) q)
    (R : ∀ q : ℕ, RationalChernClassSource B C I S q (P q) (Q q))
    (hinj : ∀ p : ℕ, Function.Injective (rationalToSmoothRealClass S p).hom)
    (hz : AllPositiveDeRhamChernZero B C P) : AllRationalChernZero B C I S P Q R := by
  intro q
  apply hinj ((2 * q + 1) + 1)
  rw [(R q).normalized, hz q, map_zero, map_zero]

end MathlibExt.AlgebraicGeometry.ManifoldRationalChernModels
