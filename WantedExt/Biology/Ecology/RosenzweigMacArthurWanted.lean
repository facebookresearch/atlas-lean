/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Rosenzweig–MacArthur model: paradox of enrichment and Cheng's unique limit cycle

Prey `S` with logistic growth rate `γ` and carrying capacity `K`, and predators `x` with Holling
type II (Monod) functional response, maximal rate `m`, half-saturation constant `a`, yield `y`
and death rate `D₀` (all positive): `S' = γ S (1 - S / K) - (m / y) x S / (a + S)` and
`x' = x (m S / (a + S) - D₀)`. With `b = m / D₀` and, for `b > 1`, `λ = a / (b - 1)`:
(i) if `b ≤ 1` or `K ≤ λ`, the predator-free equilibrium `(K, 0)` attracts every solution with
`S(0), x(0) > 0`; (ii) if `λ < K ≤ a + 2λ`, the coexistence equilibrium `(λ, x*)` with
`x* = (γ y / m) (1 - λ / K) (a + λ)` attracts every such solution; (iii) if `K > a + 2λ`,
`(λ, x*)` is unstable and there is exactly one limit cycle, which is stable (Cheng 1981,
Theorem 1). Raising `K` past `K_H = a + 2λ` destabilizes the equilibrium: Rosenzweig's paradox
of enrichment.

Recorded here: the three cases for solutions on `[0, ∞)` with positive initial densities. In
case (iii), Cheng's Theorem 1 is stated as existence, uniqueness and stability of the limit
cycle: a nonconstant periodic solution exists; every nonconstant periodic solution has its orbit;
and the orbit is stable, in that every positive solution starting close enough to it approaches
it (distance to the orbit tends to `0`). Global attraction of every positive solution other than
the equilibrium is not claimed.

Sources: K.-S. Cheng, "Uniqueness of a limit cycle for a predator-prey system", SIAM J. Math.
Anal. 12 (1981) 541–548, doi:10.1137/0512047, Theorem 1 and §1; M. L. Rosenzweig, "Paradox of
enrichment: destabilization of exploitation ecosystems in ecological time", Science 171 (1971)
385–387, doi:10.1126/science.171.3969.385; M. L. Rosenzweig and R. H. MacArthur, "Graphical
representation and stability conditions of predator-prey interactions", Am. Nat. 97 (1963)
209–223, doi:10.1086/282272.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

namespace WantedExt.Biology.Ecology.RosenzweigMacArthurWanted

open Filter Topology Metric

/-- **Rosenzweig–MacArthur parameters.** Parameters of the Rosenzweig–MacArthur model, all
positive. -/
structure Params where
  /-- Prey growth rate. -/
  γ : ℝ
  /-- Prey carrying capacity. -/
  K : ℝ
  /-- Maximal predation rate. -/
  m : ℝ
  /-- Half-saturation constant. -/
  a : ℝ
  /-- Yield (prey converted per predator). -/
  y : ℝ
  /-- Predator death rate. -/
  D₀ : ℝ
  /-- The prey growth rate is positive. -/
  γ_pos : 0 < γ
  /-- The carrying capacity is positive. -/
  K_pos : 0 < K
  /-- The maximal predation rate is positive. -/
  m_pos : 0 < m
  /-- The half-saturation constant is positive. -/
  a_pos : 0 < a
  /-- The yield is positive. -/
  y_pos : 0 < y
  /-- The predator death rate is positive. -/
  D₀_pos : 0 < D₀

namespace Params

variable (p : Params)

/-- **Rosenzweig–MacArthur vector field.** The vector field
`(γ S (1 - S/K) - (m/y) x S/(a + S), x (m S/(a + S) - D₀))` at `(S, x)`. -/
noncomputable def field (z : ℝ × ℝ) : ℝ × ℝ :=
  (p.γ * z.1 * (1 - z.1 / p.K) - p.m / p.y * z.2 * z.1 / (p.a + z.1),
    z.2 * (p.m * z.1 / (p.a + z.1) - p.D₀))

/-- **Solution of the model.** `z` solves the model on `[0, ∞)`: `z'(t) = field (z t)` for every
`t ≥ 0`. -/
def IsSolution (z : ℝ → ℝ × ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → HasDerivAt z (p.field (z t)) t

/-- **Break-even prey density.** The break-even prey density `λ = a / (m / D₀ - 1)`, meaningful
when `m > D₀`. -/
noncomputable def lam : ℝ := p.a / (p.m / p.D₀ - 1)

/-- **Coexistence equilibrium.** The coexistence equilibrium `(λ, x*)` with
`x* = (γ y / m) (1 - λ / K) (a + λ)`. -/
noncomputable def coexistenceEq : ℝ × ℝ :=
  (p.lam, p.γ * p.y / p.m * (1 - p.lam / p.K) * (p.a + p.lam))

/-- **Case (i): predator extinction.** For positive parameters with `m ≤ D₀`, or `m > D₀` and
`K ≤ λ`, every solution on `[0, ∞)` with `S(0) > 0` and `x(0) > 0` converges to
`(K, 0)`.

Source: Cheng (1981), §1. -/
public theorem_wanted tendsto_preyOnly (h : p.m ≤ p.D₀ ∨ (p.D₀ < p.m ∧ p.K ≤ p.lam))
    (z : ℝ → ℝ × ℝ) (hz : p.IsSolution z) (h₀₁ : 0 < (z 0).1) (h₀₂ : 0 < (z 0).2) :
    Tendsto z atTop (𝓝 (p.K, 0))

/-- **Case (ii): stable coexistence below the Hopf threshold.** For positive parameters with
`m > D₀` and `λ < K ≤ a + 2λ`, the coexistence equilibrium `(λ, x*)` has both coordinates positive
and every solution on `[0, ∞)` with `S(0) > 0` and `x(0) > 0` converges to it.

Source: Cheng (1981), §1. -/
public theorem_wanted tendsto_coexistenceEq (hm : p.D₀ < p.m) (h₁ : p.lam < p.K)
    (h₂ : p.K ≤ p.a + 2 * p.lam) :
    0 < p.coexistenceEq.1 ∧ 0 < p.coexistenceEq.2 ∧
      ∀ z : ℝ → ℝ × ℝ, p.IsSolution z → 0 < (z 0).1 → 0 < (z 0).2 →
        Tendsto z atTop (𝓝 p.coexistenceEq)

/-- **Case (iii): paradox of enrichment and Cheng's unique limit cycle.** For positive parameters
with `m > D₀` and `K > a + 2λ`,
(1) the coexistence equilibrium `(λ, x*)` has both coordinates positive and is Lyapunov unstable:
there is `ε > 0` such that for every `δ > 0` some solution on `[0, ∞)` with positive initial
densities starts within `δ` of it and is at distance at least `ε` at some time `t ≥ 0`;
(2) existence: there is a nonconstant periodic solution `c` with positive coordinates and period
`T > 0` (`c (t + T) = c t` for all `t ≥ 0`, and `c t ≠ c 0` for some `t ≥ 0`); (3) uniqueness:
every nonconstant periodic solution with positive initial densities has the same orbit
`{c t | t ≥ 0}`; (4) stability: there is `δ > 0` such that every solution with positive initial
densities whose initial point is within distance `δ` of this orbit approaches it, i.e. its
distance to the orbit tends to `0`.

Source: Cheng (1981), Theorem 1. -/
public theorem_wanted unique_limit_cycle (hm : p.D₀ < p.m) (hK : p.a + 2 * p.lam < p.K) :
    0 < p.coexistenceEq.1 ∧ 0 < p.coexistenceEq.2 ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ∃ z : ℝ → ℝ × ℝ, p.IsSolution z ∧ 0 < (z 0).1 ∧
        0 < (z 0).2 ∧ dist (z 0) p.coexistenceEq < δ ∧
          ∃ t : ℝ, 0 ≤ t ∧ ε ≤ dist (z t) p.coexistenceEq) ∧
      ∃ c : ℝ → ℝ × ℝ, ∃ T : ℝ, 0 < T ∧ p.IsSolution c ∧ 0 < (c 0).1 ∧ 0 < (c 0).2 ∧
        (∀ t, 0 ≤ t → c (t + T) = c t) ∧ (∃ t, 0 ≤ t ∧ c t ≠ c 0) ∧
        (∀ w : ℝ → ℝ × ℝ, ∀ T' : ℝ, 0 < T' → p.IsSolution w → 0 < (w 0).1 → 0 < (w 0).2 →
          (∀ t, 0 ≤ t → w (t + T') = w t) → (∃ t, 0 ≤ t ∧ w t ≠ w 0) →
          w '' Set.Ici 0 = c '' Set.Ici 0) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ → ℝ × ℝ, p.IsSolution z → 0 < (z 0).1 → 0 < (z 0).2 →
          infDist (z 0) (c '' Set.Ici 0) < δ →
          Tendsto (fun t => infDist (z t) (c '' Set.Ici 0)) atTop (𝓝 0)

end Params

end WantedExt.Biology.Ecology.RosenzweigMacArthurWanted
