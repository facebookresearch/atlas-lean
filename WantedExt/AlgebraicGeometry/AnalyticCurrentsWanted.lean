/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticCurrents

/-!
# A nef class of positive volume contains an actual Kähler current

Demailly--Paun, math/0105176v2, Theorem 0.4. Nefness uses closure of the
actual Kähler cone in real de Rham cohomology. Volume, representation,
closedness, type and domination use the actual forms, distributional
differential and coordinate integrals. No bigness/current oracle is input.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticCurrents

open KahlerClassGeometry ManifoldDifferentialForms CoordinateFormIntegrals
open scoped Manifold ContDiff

theorem_wanted nef_positiveVolume_kahlerCurrent
    (n : ℕ) (hn : 0 < n) (M : Type) [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [ExteriorTheory ℝ (Coordinates n) M] [FiniteDimensional ℝ (H2 n M)]
    [WedgeTheory n M] [CurrentDifferentialTheory n M]
    (R : RealCoordinateMap n) (A : IntegrationAtlas n M) [IntegrationTheory n M R A]
    (eta : KahlerStructure n M) (alpha : ClosedTwoForms n M)
    (htype : IsTypeOneOne n M alpha.val)
    (hnef : letI := cohomologyTopology n M
      classOfClosedTwoForm ℝ (Coordinates n) M alpha ∈ closure (kahlerCone n M))
    (hvolume : 0 < integral n M R A
      (castForm n M (by omega) (wedgePower n M alpha.val n))) :
    ∃ T : Current n M 2, IsTypeOneOneCurrent n M T ∧ IsClosedCurrent n M T ∧
      Represents n M R A hn T alpha ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ Dominates n M R A hn T eta.form.val epsilon

end MathlibExt.AlgebraicGeometry.AnalyticCurrents

