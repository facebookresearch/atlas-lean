/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two-species Lotka–Volterra competition: the four generic outcomes

Two competitors obey `x₁' = r₁ x₁ (1 - (x₁ + α₁₂ x₂) / K₁)` and
`x₂' = r₂ x₂ (1 - (x₂ + α₂₁ x₁) / K₂)` with positive growth rates `rᵢ`, carrying capacities `Kᵢ`
and competition coefficients `αᵢⱼ`. Away from the degenerate cases `α₁₂ = K₁ / K₂` or
`α₂₁ = K₂ / K₁`, the fate of every solution with both species initially present is: (i) if
`α₁₂ < K₁ / K₂` and `α₂₁ < K₂ / K₁`, the interior equilibrium attracts every such solution
(stable coexistence); (ii) if `α₁₂ > K₁ / K₂` and `α₂₁ > K₂ / K₁`, the system is bistable: the
interior equilibrium is a saddle and every solution tends to it or to one of `(K₁, 0)` and
`(0, K₂)`, both of which attract interior solutions; (iii) if `α₁₂ < K₁ / K₂` and
`α₂₁ > K₂ / K₁`, species `1` excludes species `2` and every solution tends to `(K₁, 0)`;
(iv) symmetrically, every solution tends to `(0, K₂)`.

Recorded here: the four cases for solutions on `[0, ∞)` with positive initial densities; in case
(ii) the saddle is stated as Lyapunov instability, and the separatrix is not formalized. The
classical primary sources (Lotka 1925; Volterra 1926; Gause 1934) and Hofbauer–Sigmund (1998,
§3.3) were not read; the case analysis follows university lecture notes on the competition
equations, and the reduction of "all interior orbits" to a rigorous argument (no periodic
orbits) is derived.

Sources: A. J. Lotka, *Elements of Physical Biology* (1925); V. Volterra, "Fluctuations in the
abundance of a species considered mathematically", Nature 118 (1926) 558–560,
doi:10.1038/118558a0; B. S. Goh, "Global stability in two species interactions", J. Math. Biol.
3 (1976) 313–318, doi:10.1007/BF00275063; J. Hofbauer and K. Sigmund, *Evolutionary Games and
Population Dynamics*, Cambridge Univ. Press (1998), §3.3.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace WantedExt.Biology.Ecology.LotkaVolterraCompetitionWanted

open Filter Topology

/-- Parameters of the two-species competition model: growth rates `rᵢ`, carrying capacities
`Kᵢ` and competition coefficients `α₁₂`, `α₂₁`, all positive. -/
structure Params where
  /-- Growth rate of species `1`. -/
  r₁ : ℝ
  /-- Growth rate of species `2`. -/
  r₂ : ℝ
  /-- Carrying capacity of species `1`. -/
  K₁ : ℝ
  /-- Carrying capacity of species `2`. -/
  K₂ : ℝ
  /-- Effect of species `2` on species `1`. -/
  α₁₂ : ℝ
  /-- Effect of species `1` on species `2`. -/
  α₂₁ : ℝ
  /-- The growth rate of species `1` is positive. -/
  r₁_pos : 0 < r₁
  /-- The growth rate of species `2` is positive. -/
  r₂_pos : 0 < r₂
  /-- The carrying capacity of species `1` is positive. -/
  K₁_pos : 0 < K₁
  /-- The carrying capacity of species `2` is positive. -/
  K₂_pos : 0 < K₂
  /-- The effect of species `2` on species `1` is positive. -/
  α₁₂_pos : 0 < α₁₂
  /-- The effect of species `1` on species `2` is positive. -/
  α₂₁_pos : 0 < α₂₁

namespace Params

variable (p : Params)

/-- The competition vector field at `(x₁, x₂)`. -/
noncomputable def field (z : ℝ × ℝ) : ℝ × ℝ :=
  (p.r₁ * z.1 * (1 - (z.1 + p.α₁₂ * z.2) / p.K₁), p.r₂ * z.2 * (1 - (z.2 + p.α₂₁ * z.1) / p.K₂))

/-- `z` solves the competition equations on `[0, ∞)`: `z'(t) = field (z t)` for every `t ≥ 0`. -/
def IsSolution (z : ℝ → ℝ × ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → HasDerivAt z (p.field (z t)) t

/-- The interior equilibrium
`((K₁ - α₁₂ K₂) / (1 - α₁₂ α₂₁), (K₂ - α₂₁ K₁) / (1 - α₁₂ α₂₁))`. -/
noncomputable def interiorEq : ℝ × ℝ :=
  ((p.K₁ - p.α₁₂ * p.K₂) / (1 - p.α₁₂ * p.α₂₁), (p.K₂ - p.α₂₁ * p.K₁) / (1 - p.α₁₂ * p.α₂₁))

/-- **Stable coexistence** (case (i)): for positive parameters with `α₁₂ < K₁ / K₂` and
`α₂₁ < K₂ / K₁`, the interior equilibrium has both coordinates positive, and every solution on
`[0, ∞)` with both initial densities positive converges to it.

Sources: Goh (1976); Hofbauer and Sigmund (1998), §3.3. -/
public theorem_wanted tendsto_interiorEq (h₁ : p.α₁₂ < p.K₁ / p.K₂) (h₂ : p.α₂₁ < p.K₂ / p.K₁) :
    0 < p.interiorEq.1 ∧ 0 < p.interiorEq.2 ∧
      ∀ z : ℝ → ℝ × ℝ, p.IsSolution z → 0 < (z 0).1 → 0 < (z 0).2 →
        Tendsto z atTop (𝓝 p.interiorEq)

/-- **Exclusion of species `2`** (case (iii)): for positive parameters with `α₁₂ < K₁ / K₂` and
`α₂₁ > K₂ / K₁`, every solution on `[0, ∞)` with both initial densities positive converges to
`(K₁, 0)`.

Source: Hofbauer and Sigmund (1998), §3.3. -/
public theorem_wanted tendsto_first (h₁ : p.α₁₂ < p.K₁ / p.K₂) (h₂ : p.K₂ / p.K₁ < p.α₂₁)
    (z : ℝ → ℝ × ℝ) (hz : p.IsSolution z) (h₀₁ : 0 < (z 0).1) (h₀₂ : 0 < (z 0).2) :
    Tendsto z atTop (𝓝 (p.K₁, 0))

/-- **Exclusion of species `1`** (case (iv)): for positive parameters with `α₁₂ > K₁ / K₂` and
`α₂₁ < K₂ / K₁`, every solution on `[0, ∞)` with both initial densities positive converges to
`(0, K₂)`.

Source: Hofbauer and Sigmund (1998), §3.3. -/
public theorem_wanted tendsto_second (h₁ : p.K₁ / p.K₂ < p.α₁₂) (h₂ : p.α₂₁ < p.K₂ / p.K₁)
    (z : ℝ → ℝ × ℝ) (hz : p.IsSolution z) (h₀₁ : 0 < (z 0).1) (h₀₂ : 0 < (z 0).2) :
    Tendsto z atTop (𝓝 (0, p.K₂))

/-- **Bistability** (case (ii)): for positive parameters with `α₁₂ > K₁ / K₂` and
`α₂₁ > K₂ / K₁`, the interior equilibrium has both coordinates positive; every solution on
`[0, ∞)` with both initial densities positive converges to `(K₁, 0)`, to `(0, K₂)` or to the
interior equilibrium; each of `(K₁, 0)` and `(0, K₂)` is the limit of some such solution; and the
interior equilibrium is Lyapunov unstable: there is `ε > 0` such that for every `δ > 0` some such
solution starts within `δ` of it and later leaves its `ε`-neighbourhood.

Source: Hofbauer and Sigmund (1998), §3.3. -/
public theorem_wanted bistable (h₁ : p.K₁ / p.K₂ < p.α₁₂) (h₂ : p.K₂ / p.K₁ < p.α₂₁) :
    0 < p.interiorEq.1 ∧ 0 < p.interiorEq.2 ∧
      (∀ z : ℝ → ℝ × ℝ, p.IsSolution z → 0 < (z 0).1 → 0 < (z 0).2 →
        Tendsto z atTop (𝓝 (p.K₁, 0)) ∨ Tendsto z atTop (𝓝 (0, p.K₂)) ∨
          Tendsto z atTop (𝓝 p.interiorEq)) ∧
      (∃ z : ℝ → ℝ × ℝ, p.IsSolution z ∧ 0 < (z 0).1 ∧ 0 < (z 0).2 ∧
        Tendsto z atTop (𝓝 (p.K₁, 0))) ∧
      (∃ z : ℝ → ℝ × ℝ, p.IsSolution z ∧ 0 < (z 0).1 ∧ 0 < (z 0).2 ∧
        Tendsto z atTop (𝓝 (0, p.K₂))) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ z : ℝ → ℝ × ℝ, p.IsSolution z ∧ 0 < (z 0).1 ∧
        0 < (z 0).2 ∧ dist (z 0) p.interiorEq < δ ∧ ∃ t : ℝ, 0 ≤ t ∧ ε ≤ dist (z t) p.interiorEq

end Params

end WantedExt.Biology.Ecology.LotkaVolterraCompetitionWanted
