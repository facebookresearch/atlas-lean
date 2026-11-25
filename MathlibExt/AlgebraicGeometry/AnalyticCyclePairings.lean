/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals
public import Mathlib.Topology.Connected.Clopen

/-!
# Actual analytic-cycle integrals and numerical positivity

Analytic sets are locally the common zero set of finitely many actual
holomorphic chart functions. A resolved irreducible cycle uses a proper
holomorphic map from a compact complex manifold, with generic degree one
and injective differential. Its pairing is the literal integral of the
pulled-back form power. It is not a numerical pairing selected as data.

Ordinary resolution, smooth pullback, wedge and Stokes adapters are source
support. The Demailly--Paun cone comparison is a separate proof request.
Reference: Demailly--Paun, math/0105176v2, Main Theorem 0.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCyclePairings

open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals
open Set TopologicalSpace
open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coordinates n) M]

/-- Locally, in the chart at each point, `Y` is the common zero set of finitely
many holomorphic functions. -/
def IsAnalyticSet (Y : Set M) : Prop :=
  ∀ x : M, ∃ (U : Opens M), x ∈ U ∧
    (U : Set M) ⊆ (extChartAt 𝓘(ℂ, Coordinates n) x).source ∧
    ∃ (r : ℕ) (f : Fin r → Coordinates n → ℂ),
      (∀ i, ContDiffOn ℂ ∞ (f i) ((extChartAt 𝓘(ℂ, Coordinates n) x) '' (U : Set M))) ∧
      Y ∩ (U : Set M) = {z | z ∈ U ∧ ∀ i, f i (extChartAt 𝓘(ℂ, Coordinates n) x z) = 0}

/-- `Y` is nonempty and not covered by two analytic sets unless one of them
already contains it. This is irreducibility relative to analytic sets; it does
not ask `Y` itself to be analytic, which `ResolvedCycle` requires separately. -/
def IrreducibleAnalytic (Y : Set M) : Prop :=
  Y.Nonempty ∧ ∀ A B : Set M,
    IsAnalyticSet n M A → IsAnalyticSet n M B → Y ⊆ A ∪ B → Y ⊆ A ∨ Y ⊆ B

variable (d : ℕ) (Y : Type) [TopologicalSpace Y] [ChartedSpace (Coordinates d) Y]

def pullbackRough (f : Y → M) {p : ℕ}
    (a : RoughForm ℝ (Coordinates n) M ⊤ p) :
    RoughForm ℝ (Coordinates d) Y ⊤ p :=
  fun y ↦ (a ⟨f y.val, by trivial⟩).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Coordinates d) 𝓘(ℝ, Coordinates n) f y.val)

/-- For a map $f : Y → M$ between spaces charted on $ℂ^d$ and $ℂ^n$: an instance asserts that,
for every $p$ and every smooth real $p$-form $a$ on $M$, the pointwise pullback of $a$ along $f$
through the real manifold derivative of $f$ (`pullbackRough`) is a smooth form on $Y$. -/
class PullbackTheory (f : Y → M) : Prop where
  smooth : ∀ p (a : GlobalForms ℝ (Coordinates n) M p),
    IsSmooth ℝ (Coordinates d) Y (pullbackRough n M d Y f a.val)

def pullbackForms (f : Y → M) [PullbackTheory n M d Y f] (p : ℕ) :
    Forms n M p →ₗ[ℝ] Forms d Y p where
  toFun a := ⟨pullbackRough n M d Y f a.val, PullbackTheory.smooth p a⟩
  map_add' a b := by
    apply Subtype.ext
    ext y v
    rfl
  map_smul' c a := by
    apply Subtype.ext
    ext y v
    rfl

/-- A genuine resolution of a closed analytic cycle. The exceptional image
is a proper analytic subset; the generic map has degree one. -/
structure ResolvedCycle
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates d) ∞ Y] where
  support : Set M
  analytic : IsAnalyticSet n M support
  closed : IsClosed support
  irreducible : IrreducibleAnalytic n M support
  map : Y → M
  holomorphic : ContMDiff 𝓘(ℂ, Coordinates d) 𝓘(ℂ, Coordinates n) ∞ map
  proper : IsProperMap map
  image : Set.range map = support
  exceptional : Set M
  exceptional_analytic : IsAnalyticSet n M exceptional
  exceptional_proper : support ∩ exceptional ≠ support
  generic_injective : Set.InjOn map (map ⁻¹' (support \ exceptional))
  generic_derivative : ∀ y, map y ∉ exceptional →
    Function.Injective (mfderiv 𝓘(ℂ, Coordinates d) 𝓘(ℂ, Coordinates n) map y)
  generic_dense : Dense (map ⁻¹' (support \ exceptional))

variable [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
  [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates d) ∞ Y]
  [IsManifold 𝓘(ℂ, Coordinates d) ∞ Y]
  [ExteriorTheory ℝ (Coordinates d) Y] [WedgeTheory d Y]

def cycleIntegral (C : ResolvedCycle n M d Y)
    [PullbackTheory n M d Y C.map]
    (R : RealCoordinateMap d) (A : IntegrationAtlas d Y)
    (a : ClosedTwoForms n M) : ℝ :=
  integral d Y R A (castForm d Y (by omega)
    (wedgePower d Y (pullbackForms n M d Y C.map 2 a.val) d))

variable [FiniteDimensional ℝ (H2 n M)]

/-- All closed representatives are tested against all genuine resolved
analytic cycles. Ordinary Stokes identifies their displayed integrals. -/
def numericallyPositive (a : H2 n M) : Prop :=
  a ∈ realOneOneClasses n M ∧
  ∀ (alpha : ClosedTwoForms n M), classOfClosedTwoForm ℝ (Coordinates n) M alpha = a →
    ∀ (d : ℕ), 0 < d → d ≤ n →
    ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
      [ChartedSpace (Coordinates d) Y]
      [IsManifold 𝓘(ℝ, Coordinates d) ∞ Y] [IsManifold 𝓘(ℂ, Coordinates d) ∞ Y]
      [ExteriorTheory ℝ (Coordinates d) Y] [WedgeTheory d Y]
      (C : ResolvedCycle n M d Y) [PullbackTheory n M d Y C.map]
      (R : RealCoordinateMap d) (A : IntegrationAtlas d Y)
      [IntegrationTheory d Y R A],
      0 < cycleIntegral n M d Y C R A alpha

def positiveSet : Set (H2 n M) := {a | numericallyPositive n M a}

end MathlibExt.AlgebraicGeometry.AnalyticCyclePairings
