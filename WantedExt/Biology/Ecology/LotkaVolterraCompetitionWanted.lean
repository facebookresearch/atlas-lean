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
(ii) the saddle is stated as Lyapunov instability, and the separatrix is not formalized. The four
cases follow S.-B. Hsu, lecture notes §3.12 "Competition models, Mutualism or Symbiosis" (National
Tsing Hua University); the global convergence of all interior orbits (ruling out periodic orbits
in the open quadrant) is derived from that phase-plane analysis. In `Fin 2 → ℝ` coordinates the
competition equations are the Lotka–Volterra system `IsLVSolution` (with the library's field
`lvField`) for growth rates `(r₁, r₂)` and the interaction matrix `C` with entries `-r₁ / K₁`,
`-r₁ α₁₂ / K₁`, `-r₂ α₂₁ / K₂`, `-r₂ / K₂`: `isSolution_iff_isLVSolution` states the equivalence.

Sources: S.-B. Hsu, lecture notes, §3.12 "Competition models, Mutualism or Symbiosis" (National
Tsing Hua University); background references (not directly consulted): A. J. Lotka (1925),
V. Volterra (1926), B. S. Goh (1976), J. Hofbauer and K. Sigmund (1998).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Biology.Ecology.LotkaVolterraNoInteriorEquilibriumWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace WantedExt.Biology.Ecology.LotkaVolterraCompetitionWanted

open Filter Topology
open LotkaVolterraNoInteriorEquilibriumWanted (IsLVSolution)
open MathlibExt.Biology.Dynamics.ReplicatorLotkaVolterra (lvField)

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

/-- **The competition vector field.** At `z = (x₁, x₂)` it is
`(r₁ x₁ (1 - (x₁ + α₁₂ x₂) / K₁), r₂ x₂ (1 - (x₂ + α₂₁ x₁) / K₂))`: the coefficient `α₁₂` weighs
the effect of species `2` on the growth of species `1`, and `α₂₁` the effect of species `1` on
species `2`. -/
noncomputable def field (z : ℝ × ℝ) : ℝ × ℝ :=
  (p.r₁ * z.1 * (1 - (z.1 + p.α₁₂ * z.2) / p.K₁), p.r₂ * z.2 * (1 - (z.2 + p.α₂₁ * z.1) / p.K₂))

/-- **Forward solutions of the competition equations.** `z` solves the competition equations at
every time `t ≥ 0`: `z'(t) = field (z t)`. The derivative is two-sided (`HasDerivAt`) at `t = 0`
too, so a trajectory given only on `[0, ∞)` must be extended to negative times with that
derivative at `0`; one that is only right-differentiable at `0` does not qualify. A solution on an
open interval containing `[0, ∞)` qualifies, and negative times matter only through the
derivative at `0`. Equivalently, `t ↦ ![(z t).1, (z t).2]` solves the Lotka–Volterra system
`IsLVSolution` (`isSolution_iff_isLVSolution`). -/
def IsSolution (z : ℝ → ℝ × ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → HasDerivAt z (p.field (z t)) t

/-- **The competition equations as a Lotka–Volterra system.** `z` solves the competition
equations (`IsSolution`) exactly when the curve `t ↦ ![(z t).1, (z t).2]` in `Fin 2 → ℝ` solves
the Lotka–Volterra system `yᵢ' = yᵢ (rᵢ + ∑ⱼ Cᵢⱼ yⱼ)` (`IsLVSolution`, with the library's field
`lvField`) for growth rates `(r₁, r₂)` and the interaction matrix `C` with rows
`(-r₁ / K₁, -r₁ α₁₂ / K₁)` and `(-r₂ α₂₁ / K₂, -r₂ / K₂)`. Both predicates ask for two-sided
derivatives at every time `t ≥ 0`, so results stated for `IsLVSolution` apply to the competition
model. -/
theorem isSolution_iff_isLVSolution (z : ℝ → ℝ × ℝ) :
    p.IsSolution z ↔
      IsLVSolution ![p.r₁, p.r₂]
        !![-p.r₁ / p.K₁, -(p.r₁ * p.α₁₂) / p.K₁; -(p.r₂ * p.α₂₁) / p.K₂, -p.r₂ / p.K₂]
        (fun t => ![(z t).1, (z t).2]) := by
  have hfield (w : ℝ × ℝ) :
      lvField ![p.r₁, p.r₂]
          !![-p.r₁ / p.K₁, -(p.r₁ * p.α₁₂) / p.K₁; -(p.r₂ * p.α₂₁) / p.K₂, -p.r₂ / p.K₂]
          ![w.1, w.2] = ![(p.field w).1, (p.field w).2] := by
    ext i
    fin_cases i <;> simp [lvField, field, Fin.sum_univ_two] <;> ring
  have hderiv (v : ℝ × ℝ) (t : ℝ) :
      HasDerivAt z v t ↔ HasDerivAt (fun s => ![(z s).1, (z s).2]) ![v.1, v.2] t := by
    rw [hasDerivAt_pi, Fin.forall_fin_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩
  refine forall₂_congr fun t _ => ?_
  rw [hfield, ← hderiv]

/-- The candidate algebraic formula
`((K₁ - α₁₂ K₂) / (1 - α₁₂ α₂₁), (K₂ - α₂₁ K₁) / (1 - α₁₂ α₂₁))` for a coexistence equilibrium.
It defines a positive interior equilibrium when `α₁₂ α₂₁ ≠ 1` and both quotients are positive (as
in the strict coexistence and bistability regimes); when `α₁₂ α₂₁ = 1`, totalized division by zero
gives `(0, 0)`. -/
noncomputable def interiorEq : ℝ × ℝ :=
  ((p.K₁ - p.α₁₂ * p.K₂) / (1 - p.α₁₂ * p.α₂₁), (p.K₂ - p.α₂₁ * p.K₁) / (1 - p.α₁₂ * p.α₂₁))

/-- **Stable coexistence**: for positive parameters with `α₁₂ < K₁ / K₂` and
`α₂₁ < K₂ / K₁`, the interior equilibrium has both coordinates positive, and every solution on
`[0, ∞)` with both initial densities positive converges to it.

Source: S.-B. Hsu, lecture notes, §3.12 "Competition models, Mutualism or Symbiosis" (NTHU),
case (iii) / Fig. 12.3 (global convergence over all interior orbits derived from the planar phase
analysis). -/
public theorem_wanted tendsto_interiorEq (h₁ : p.α₁₂ < p.K₁ / p.K₂) (h₂ : p.α₂₁ < p.K₂ / p.K₁) :
    0 < p.interiorEq.1 ∧ 0 < p.interiorEq.2 ∧
      ∀ z : ℝ → ℝ × ℝ, p.IsSolution z → 0 < (z 0).1 → 0 < (z 0).2 →
        Tendsto z atTop (𝓝 p.interiorEq)

/-- **Exclusion of species `2`** (first species wins): for positive parameters with
`α₁₂ < K₁ / K₂` and `α₂₁ > K₂ / K₁`, every solution on `[0, ∞)` with both initial densities
positive converges to `(K₁, 0)`.

Source: S.-B. Hsu, lecture notes, §3.12 "Competition models, Mutualism or Symbiosis" (NTHU),
case (ii) / Fig. 12.2 (global convergence over all interior orbits derived from the planar phase
analysis). -/
public theorem_wanted tendsto_first (h₁ : p.α₁₂ < p.K₁ / p.K₂) (h₂ : p.K₂ / p.K₁ < p.α₂₁)
    (z : ℝ → ℝ × ℝ) (hz : p.IsSolution z) (h₀₁ : 0 < (z 0).1) (h₀₂ : 0 < (z 0).2) :
    Tendsto z atTop (𝓝 (p.K₁, 0))

/-- **Exclusion of species `1`** (second species wins): for positive parameters with
`α₁₂ > K₁ / K₂` and `α₂₁ < K₂ / K₁`, every solution on `[0, ∞)` with both initial densities
positive converges to `(0, K₂)`.

Source: S.-B. Hsu, lecture notes, §3.12 "Competition models, Mutualism or Symbiosis" (NTHU),
case (i) / Fig. 12.1 (global convergence over all interior orbits derived from the planar phase
analysis). -/
public theorem_wanted tendsto_second (h₁ : p.K₁ / p.K₂ < p.α₁₂) (h₂ : p.α₂₁ < p.K₂ / p.K₁)
    (z : ℝ → ℝ × ℝ) (hz : p.IsSolution z) (h₀₁ : 0 < (z 0).1) (h₀₂ : 0 < (z 0).2) :
    Tendsto z atTop (𝓝 (0, p.K₂))

/-- **Bistability**: for positive parameters with `α₁₂ > K₁ / K₂` and `α₂₁ > K₂ / K₁`, the
interior equilibrium has both coordinates positive; every solution on `[0, ∞)` with both initial
densities positive converges to `(K₁, 0)`, to `(0, K₂)` or to the interior equilibrium; each of
`(K₁, 0)` and `(0, K₂)` is the limit of some such solution; and the interior equilibrium is
Lyapunov unstable: there is `ε > 0` such that for every `δ > 0` some such solution starts within
`δ` of it and later leaves its `ε`-neighbourhood.

Source: S.-B. Hsu, lecture notes, §3.12 "Competition models, Mutualism or Symbiosis" (NTHU),
case (iv) / Fig. 12.4 (Lyapunov instability and trichotomy derived from the planar phase
analysis). -/
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
