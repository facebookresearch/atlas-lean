/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Time averages of interior replicator orbits converge to the interior rest point

For the replicator equation `xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)` with a unique rest point `p` in the
interior of the simplex, the time averages `(1/T) ∫₀ᵀ x(t) dt` along every interior orbit that
stays bounded away from the boundary converge to `p` (Schuster, Sigmund, Hofbauer and Wolff 1981,
§5, statement B; restated by Hofbauer and Sigmund 2003, Theorem 4, for permanent systems). The
proof integrates `(ln xᵢ)' - (ln xⱼ)' = (A x)ᵢ - (A x)ⱼ`: the left side divided by `T` tends to
`0` because the orbit stays in a compact subset of the interior, so every limit point of the
averages is an interior rest point. For the predator–prey case this contains Volterra's law of
averages.

The replicator equation and its rest points are the library predicates `IsSolution` and
`IsRestPoint` of `MathlibExt.Biology.Dynamics.Replicator` (`MathlibExt.Dynamics.Replicator.Basic`).

Recorded here: convergence of the time averages for solutions on `[0, ∞)` whose coordinates stay
above a fixed `δ > 0`. Volterra's third law (the effect of harvesting) is not formalized.

Sources: P. Schuster, K. Sigmund, J. Hofbauer and R. Wolff, "Selfregulation of behaviour in
animal societies. I. Symmetric contests", Biol. Cybern. 40 (1981) 1–8, §5; J. Hofbauer and
K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.) 40 (2003) 479–519,
doi:10.1090/S0273-0979-03-00988-1, Theorem 4.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.Replicator.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.ReplicatorTimeAverageWanted

open Filter Topology Matrix MathlibExt.Biology.Dynamics.Replicator

/-- `z` is an **interior rest point** of the replicator equation of the matrix game `A`: every
`zᵢ > 0`, `∑ zᵢ = 1`, and `z` is a rest point, `IsRestPoint (fun z => A *ᵥ z) z` (since every
`zᵢ > 0`, every strategy then earns the mean payoff `(A z)ᵢ = zᵀ A z`). -/
def IsInteriorRestPoint {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : Prop :=
  (∀ i, 0 < z i) ∧ ∑ i, z i = 1 ∧ IsRestPoint (fun z => A *ᵥ z) z

/-- **Convergence of time averages** (Schuster, Sigmund, Hofbauer and Wolff 1981, §5 B; Hofbauer
and Sigmund 2003, Theorem 4): let `A` be a real square matrix indexed by a finite type, and
suppose `p` is the unique interior rest point of the replicator equation
`xᵢ' = xᵢ ((A x)ᵢ - xᵀ A x)`. Let `x` be a solution (`IsSolution (fun z => A *ᵥ z) x`) with
`x(0)` in the interior of the simplex (every `xᵢ(0) > 0`, `∑ xᵢ(0) = 1`) that stays bounded
away from the boundary: there is `δ > 0` with `xᵢ(t) ≥ δ` for every `i` and every `t ≥ 0`. Then
for every `i`, the time average `(1/T) ∫₀ᵀ xᵢ(t) dt` converges to `pᵢ` as `T → ∞`. Here
`IsSolution` asks for two-sided derivatives at every `t ≥ 0`, `t = 0` included: a trajectory
given only on `[0, ∞)` must be extended to negative times with the replicator derivative at `0`.
Hofbauer and Sigmund (2003, Theorem 4) state this for permanent systems; the hypotheses
here are instead a unique interior rest point and an orbit bounded away from the boundary.

Sources: Schuster, Sigmund, Hofbauer and Wolff (1981), §5; Hofbauer and Sigmund (2003),
Theorem 4. -/
public theorem_wanted tendsto_timeAverage {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (p : ι → ℝ) (hp : IsInteriorRestPoint A p) (huniq : ∀ z, IsInteriorRestPoint A z → z = p)
    (x : ℝ → ι → ℝ) (hx : IsSolution (fun z => A *ᵥ z) x) (hx₀ : (∀ i, 0 < x 0 i) ∧ ∑ i, x 0 i = 1)
    (δ : ℝ) (hδ : 0 < δ) (hbdd : ∀ t : ℝ, 0 ≤ t → ∀ i, δ ≤ x t i) (i : ι) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, x t i) atTop (𝓝 (p i))

end WantedExt.Biology.Ecology.ReplicatorTimeAverageWanted
