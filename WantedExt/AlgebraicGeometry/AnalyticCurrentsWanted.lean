/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticCurrents
public import MathlibExt.AlgebraicGeometry.AnalyticCurrentsCurrentDifferentialTheory

/-!
# A nef class of positive volume contains an actual Kähler current

Demailly--Paun, math/0105176v2, Theorem 0.4 (Theorem 0.5 of the published
version, Ann. of Math. 159 (2004)). Nefness uses closure of the
actual Kähler cone in real de Rham cohomology. Volume, representation,
closedness, type and domination use the actual forms, distributional
differential and coordinate integrals. No bigness/current oracle is input.
The boundedness of the distributional differential, a hypothesis class in
`MathlibExt`, is proved in
`MathlibExt.AlgebraicGeometry.AnalyticCurrentsCurrentDifferentialTheory`.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticCurrentsWanted

open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals AnalyticCurrents
open scoped Manifold ContDiff

/-- Demailly–Păun, Theorem 0.4 (0.5 in the published version): let $M$ be a compact, connected,
second-countable Hausdorff complex manifold of dimension $n > 0$ (charts in $\mathbb{C}^n$, smooth
as a real and as a complex manifold) whose second real de Rham cohomology is finite-dimensional,
with a chosen Kähler form $\eta$, assuming the laws of the exterior derivative and the wedge
product, that the distributional differential of a current is a current, and the laws of
coordinate integration (`ExteriorTheory`, `WedgeTheory`, `CurrentDifferentialTheory`,
`IntegrationTheory`, the last for a chosen real coordinate map `R` and integration atlas `A`).
Let $\alpha$ be a closed real 2-form, not necessarily of type (1,1) pointwise, whose class lies in
the closure of the Kähler cone and with $\int_M \alpha^n > 0$. Then there are a closed current $T$
of degree 2 and type (1,1) representing the class of $\alpha$ ($T - \alpha = dS$ for a current $S$
of degree 1) and $\varepsilon > 0$ with $T(\beta) \ge \varepsilon \int_M \eta \wedge \beta$ for
every positive test form $\beta$. -/
public theorem_wanted nef_positiveVolume_kahlerCurrent
    (n : ℕ) (hn : 0 < n) (M : Type) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] [FiniteDimensional ℝ (H2 n M)]
    [WedgeTheory n M] [CurrentDifferentialTheory n M]
    (R : RealCoordinateMap n) (A : IntegrationAtlas n M) [IntegrationTheory n M R A]
    (eta : KahlerStructure n M) (alpha : ClosedTwoForms n M)
    (hnef : letI := cohomologyTopology n M
      classOfClosedTwoForm ℝ (Coordinates n) M alpha ∈ closure (kahlerCone n M))
    (hvolume : 0 < integral n M R A
      (castForm n M (by omega) (wedgePower n M alpha.val n))) :
    ∃ T : Current n M 2, IsTypeOneOneCurrent n M T ∧ IsClosedCurrent n M T ∧
      Represents n M R A hn T alpha ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ Dominates n M R A hn T eta.form.val epsilon

end WantedExt.AlgebraicGeometry.AnalyticCurrentsWanted
