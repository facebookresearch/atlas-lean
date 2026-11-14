/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

/-!
# The unipotent curve Hodge-module boundary construction

This packet requests concrete good-filtration and de Rham comparisons for
the source-specified Deligne/minimal-extension model. It supplies no named
predicate or arbitrary category called mixed Hodge modules, and repeats no
limiting-MHS theorem. Sources: Saito, *Modules de Hodge polarisables* (1988),
§3.2; Schnell, https://arxiv.org/abs/1405.3096, §18, Parts 1 and 2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HodgeModuleCurveExtensionWanted

open CategoryTheory CategoryTheory.Limits
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures
open MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

/-- The actual Hodge filtration is good, including order compatibility and
eventual generation, as well as finite steps and exhaustion. -/
public theorem_wanted minimal_extension_good_hodge_filtration
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (E : PeriodExtension C e H b) : GoodHodgeFiltration C e H b E

/-- The constructed differential module has no nonzero boundary-supported
quotient: a stable submodule agreeing after inverting the actual parameter
is already the entire minimal extension. -/
public theorem_wanted minimal_extension_no_boundary_quotient
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries))
    (hP : P ≤ minimalModule C e H b)
    (hstable : ∀ v, v ∈ P → formalConnection C e H b v ∈ P)
    (hgeneric : ∀ v, v ∈ minimalModule C e H b → ∃ n : ℕ,
      (algebraMap LocalPowerSeries LocalMeromorphicSeries PowerSeries.X) ^ n • v ∈ P) :
    P = minimalModule C e H b

/-- Specialization of the completed geometric Hodge lattice has exactly
the limiting Hodge fiber, with no chosen unrelated filtration. -/
public theorem_wanted deligne_lattice_hodge_specialization
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (E : PeriodExtension C e H b) (p : ℤ) :
    ((hodgeLattice C e H b E p).restrictScalars ℂ).map (specialization C e) = E.F 0 (-p)

/-- The local minimal-extension de Rham complex realizes the IC boundary
stalk: its unshifted degree-zero cohomology is exactly the horizontal
invariant kernel, and higher cohomology vanishes. The normalization fixes
the comparison to the actual constant Laurent series of those invariants. -/
public def_wanted minimal_extension_ic_deRham
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0) :
    {η : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        (ModuleCat.of ℂ (LinearMap.ker (complexLog C e H b))) ⟶
          minimalDeRhamComplex C e H b //
      QuasiIso η ∧ ∀ v : LinearMap.ker (complexLog C e H b), ∀ i : Fin r,
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          (ModuleCat.of ℂ (LinearMap.ker (complexLog C e H b)))).inv ≫ η.f 0) v).1 i =
            algebraMap ℂ LocalMeromorphicSeries (e v.1 i)}

end WantedExt.AlgebraicGeometry.HodgeModuleCurveExtensionWanted
