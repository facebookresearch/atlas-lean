/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SmoothDeRhamBettiBridge

/-!
# Calculus of the chart-defined differential forms

`MathlibExt` defines the exterior derivative, the wedge product and the
partition-of-unity integral of forms on a manifold by explicit chart formulas,
and records their basic laws as the hypothesis classes `ExteriorTheory`,
`LocalExteriorTheory`, `WedgeTheory` and `IntegrationTheory`; every definition
and request using them is conditional on them. Request that they hold on every
smooth real or complex manifold: the exterior derivative of a smooth form is
smooth, linear, natural under restriction and squares to zero; the pointwise
wedge of smooth forms is smooth; and the chart integral of a top form on a
compact complex manifold is linear and satisfies Stokes' theorem.

Sources: J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14
(Theorem 14.24) and Chapter 16 (Theorem 16.11). TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9 proves the corresponding facts for
its own differential-form API (`TauCeti/Geometry/Manifold/DifferentialForm/`).
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ManifoldDifferentialFormsWanted

open MathlibExt.AlgebraicGeometry
open ManifoldDifferentialForms KahlerClassGeometry CoordinateFormIntegrals
open HyperkahlerComplexStructures SmoothDeRhamBettiBridge
open scoped Manifold ContDiff

/-- **Linearity and Stokes' theorem for the chart integral of top forms.** Let $M$ be a manifold
modelled on $\mathbb{C}^n$ that is smooth both as a real and as a complex manifold, assuming the
basic laws of the chart exterior derivative (`ExteriorTheory`); let $C$ identify $\mathbb{R}^{2n}$
with $\mathbb{C}^n$ along the standard real frame, and $A$ be a finite smooth partition of unity
whose weights are nonnegative, with compact supports inside the charts at their centres. Then for
the integral of a smooth $2n$-form, the sum over $A$ of the Lebesgue integrals of its weighted
chart densities, every chart density is integrable, the integral is $\mathbb{R}$-linear, and it
vanishes on $d\beta$ for every smooth $(2n-1)$-form $\beta$ (`IntegrationTheory n M C A`). -/
public theorem_wanted integrationTheory (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] [ExteriorTheory ℝ (Coordinates n) M]
    (C : RealCoordinateMap n) (A : IntegrationAtlas n M) :
    IntegrationTheory n M C A

/-- The exterior derivative of smooth global forms on a smooth manifold over
`ℝ` or `ℂ` is smooth, linear and squares to zero. -/
public instance_wanted exteriorTheory (k : Type) [RCLike k] (E : Type)
    [NormedAddCommGroup E] [NormedSpace k E] (M : Type) [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(k, E) ∞ M] :
    ExteriorTheory k E M

/-- The same for smooth forms on every open set, together with naturality
under restriction. -/
public instance_wanted localExteriorTheory (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Ambient n) M] [IsManifold 𝓘(ℝ, Ambient n) ∞ M] :
    LocalExteriorTheory n M

/-- The pointwise wedge of smooth forms is smooth, and the constant function
`1` is a smooth `0`-form. -/
public instance_wanted wedgeTheory (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Coordinates n) M] [IsManifold 𝓘(ℝ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] :
    WedgeTheory n M

end WantedExt.AlgebraicGeometry.ManifoldDifferentialFormsWanted
