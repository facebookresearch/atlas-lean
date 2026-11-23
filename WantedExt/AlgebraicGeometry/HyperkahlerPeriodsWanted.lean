/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.HyperkahlerPeriods

/-!
# Geometric BBF, period and birational Teichmüller targets

Huybrechts, alg-geom/9705025v1, sections 1.9/1.11, for the independently
read Beauville quadratic normalization and positive rational Fujiki constant;
Verbitsky, 0908.4121v8, Theorems 1.15/1.17 and Definition 1.8, for periods
and birational Teichmüller geometry. All carriers, native
coefficient/de Rham class formulas, wedge/integral normalization, actual
markings, period-line predicates and manifold-presentation normalizations
are fixed in MathlibExt. These requests construct their source providers
and prove the normalized geometric conclusions, including the native
diffeomorphism of every actual connected component.

The BBF, period and Torelli requests are stated for a reference atlas of `M`
with holomorphic transitions (`[IsManifold 𝓘(ℂ, Ambient n) ∞ M]`), for
instance the charts of one of the hyperkähler complex structures; every
compact hyperkähler manifold has such an atlas, compatible with its smooth
structure. This is a specialization, used only to orient the chart integrals
coherently: an arbitrary smooth reference atlas would not do, since a reflected
chart can cancel the partition integral while keeping `IntegrationTheory`. The
complex structures in the requests still range over all hyperkähler
structures on the underlying smooth manifold compatible with the fixed
orientation.

Ordinary de Rham and coefficient targets below are specific native
source-integration adapters. They do not re-request the already completed
normed-space exterior derivative, scalar tensor or sheafification primitives.
Primitivity is bilinear, not diagonal; the total BBF form is not a full
Hodge polarization; no arbitrary Hodge-isometry Torelli implication is used.
The malformed printed v8(1.1) is separate and is not a BBF/provider condition.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HyperkahlerPeriodsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry
open ManifoldDifferentialForms KahlerClassGeometry CoordinateFormIntegrals
open HyperkahlerComplexStructures SmoothDeRhamBettiBridge BeauvilleBogomolovForms HyperkahlerPeriods
open scoped Manifold ContDiff TensorProduct

def_wanted real_deRham_resolution (n : ℕ) (M : Type) [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    [LocalExteriorTheory n M] : DeRhamResolution n M

theorem_wanted real_deRham_class_proofs (n : ℕ) (M : Type) [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    [LocalExteriorTheory n M] (R : DeRhamResolution n M) : DeRhamClassProofs n M R

def_wanted real_deRham_comparison (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    [LocalExteriorTheory n M] (R : DeRhamResolution n M) : RealDeRhamComparison n M R

theorem_wanted integer_coefficients (M : Type) [TopologicalSpace M] : IntegerCoefficientTheory M

def_wanted integral_real_comparison (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R) : IntegralRealComparison n M R B

theorem_wanted isotopy_equivalence (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Ambient n) M] [IsManifold 𝓘(ℝ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] : Equivalence (isotopyRelation n M)

theorem_wanted unseparated_equivalence (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    (_positive : 0 < n) (_I : HyperkahlerStructures n M) : Equivalence (unseparated n M)

theorem_wanted birational_hausdorff (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [ExteriorTheory ℝ (Ambient n) M]
    (_positive : 0 < n) (_I : HyperkahlerStructures n M) : T2Space (BirationalTeich n M)

set_option maxHeartbeats 1500000 in
-- The native sheaf-derived BBF signature is large; this is type elaboration.
def_wanted bbf_form (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (_I : HyperkahlerStructures n M) : BBFForm n M C A R B positive

def_wanted marked_period_point (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (Q : BBFForm n M C A R B positive) (J : IntegralRealComparison n M R B)
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L]
    (q : LinearMap.BilinForm ℤ L) (m : Marking n M C A R B Q L q)
    (I : HyperkahlerStructures n M) :
    {p : PeriodPoint L q // p.val.submodule =
      Submodule.span ℂ {markedSymplecticClass n M C A R B J L q m I}}

def_wanted marked_period_map (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (Q : BBFForm n M C A R B positive) (J : IntegralRealComparison n M R B)
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L]
    (q : LinearMap.BilinForm ℤ L) (m : Marking n M C A R B Q L q)
    (_I : HyperkahlerStructures n M) :
    NormalizedPeriodMap n M C A R B Q J L q m

def_wanted quadric_period_atlas (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (Q : BBFForm n M C A R B positive) (J : IntegralRealComparison n M R B)
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L]
    (q : LinearMap.BilinForm ℤ L) (_m : Marking n M C A R B Q L q)
    (_I : HyperkahlerStructures n M) :
    QuadricPeriodAtlas L q

def_wanted birational_teich_atlas (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (Q : BBFForm n M C A R B positive) (J : IntegralRealComparison n M R B)
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L]
    (q : LinearMap.BilinForm ℤ L) (_m : Marking n M C A R B Q L q)
    (_I : HyperkahlerStructures n M) (a : BirationalTeich n M) :
    SmoothTeichAtlas n M (PeriodDimension L) a

def_wanted birational_torelli (n : ℕ) (M : Type) [TopologicalSpace M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
    [ConnectedSpace M] [SimplyConnectedSpace M] [ChartedSpace (Ambient n) M]
    [IsManifold 𝓘(ℝ, Ambient n) ∞ M] [IsManifold 𝓘(ℂ, Ambient n) ∞ M]
    [ExteriorTheory ℝ (Ambient n) M] [WedgeTheory (2 * n) M]
    (C : RealCoordinateMap (2 * n)) (A : IntegrationAtlas (2 * n) M)
    [IntegrationTheory (2 * n) M C A] [LocalExteriorTheory n M] [IntegerCoefficientTheory M]
    (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (positive : 0 < n) (Q : BBFForm n M C A R B positive) (J : IntegralRealComparison n M R B)
    (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L]
    (q : LinearMap.BilinForm ℤ L) (m : Marking n M C A R B Q L q)
    (_I : HyperkahlerStructures n M) (a : BirationalTeich n M)
    (F : NormalizedPeriodMap n M C A R B Q J L q m)
    (T : SmoothTeichAtlas n M (PeriodDimension L) a) (P : QuadricPeriodAtlas L q) :
    TorelliDiffeomorphism n M C A R B Q J L q m a F T P

end WantedExt.AlgebraicGeometry.HyperkahlerPeriodsWanted
