/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The folk theorem of evolutionary game dynamics

For a symmetric matrix game `A` and the replicator equation `ẋ_i = x_i ((A x)_i - x · A x)` on
the simplex `Δ`, Hofbauer and Sigmund (2003, §2.3) state the folk theorem: (a) a Nash
equilibrium is a rest point; (b) a strict Nash equilibrium is asymptotically stable; (c) a rest
point that is the limit of an interior orbit is a Nash equilibrium; (d) a stable (Lyapunov
stable) rest point is a Nash equilibrium. Part (b) follows from the asymptotic stability of
every ESS (a strict Nash equilibrium is an ESS), recorded in
`WantedExt.Biology.Ecology.BoundaryESSStabilityWanted`; it is restated here as a corollary.

The simplex, replicator field and solution predicate are shared with
`WantedExt.Biology.Ecology.BoundaryESSStabilityWanted`. The related interior-ESS development
lives in `Domains.Biology.Dynamics.ReplicatorStability`.

Sources: J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc.
(N.S.) 40 (2003) 479–519, §2.3, p. 482 (statement (a)–(d)), eq. (2), p. 481.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Ecology.EvolutionaryFolkTheoremLyapunovStable
public import WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

@[expose] public section

namespace WantedExt.Biology.Ecology.EvolutionaryFolkTheoremWanted

open Matrix Filter Topology
open WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

variable {ι : Type*} [Fintype ι]

/-- `p` is a **strict Nash equilibrium** of `A`: `p ∈ Δ` and `q · A p < p · A p` for every
`q ∈ Δ` with `q ≠ p`. -/
def IsStrictNash (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧ ∀ q ∈ simplex ι, q ≠ p → q ⬝ᵥ A *ᵥ p < p ⬝ᵥ A *ᵥ p

/-- **Folk theorem (a)** (Hofbauer and Sigmund 2003, §2.3). For every payoff matrix `A` and
every Nash equilibrium `p` of `A`, `p` is a rest point of the replicator equation:
`F(p) = 0`.

Source: Hofbauer and Sigmund (2003), §2.3, p. 482. -/
public theorem_wanted IsNash.replicatorField_eq_zero {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsNash A p) : replicatorField A p = 0

/-- **Folk theorem (b)**, a corollary of the asymptotic stability of every ESS (Hofbauer and
Sigmund 2003, §2.3). For every payoff matrix `A` and every strict Nash equilibrium `p` of `A`,
`p` is Lyapunov stable on `Δ`, and there is `δ > 0` such that every solution of the replicator
equation starting in `Δ` within `δ` of `p` converges to `p`.

Source: Hofbauer and Sigmund (2003), §2.3, p. 482. -/
public theorem_wanted IsStrictNash.asymptoticallyStable {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsStrictNash A p) :
    IsLyapunovStable A p ∧ ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x →
      x 0 ∈ simplex ι → ‖x 0 - p‖ < δ → Tendsto x atTop (𝓝 p)

/-- **Folk theorem (c)** (Hofbauer and Sigmund 2003, §2.3). For every payoff matrix `A`, if a
solution `x` of the replicator equation starts at an interior state (`x 0 ∈ Δ` and `x 0 i > 0`
for all `i`) and converges to `p` as `t → ∞`, then `p` is a Nash equilibrium of `A`.

Source: Hofbauer and Sigmund (2003), §2.3, p. 482. -/
public theorem_wanted isNash_of_tendsto {A : Matrix ι ι ℝ} {x : ℝ → ι → ℝ} {p : ι → ℝ}
    (hx : IsReplicatorSolution A x) (hx₀ : x 0 ∈ simplex ι) (hpos : ∀ i, 0 < x 0 i)
    (hlim : Tendsto x atTop (𝓝 p)) : IsNash A p

end WantedExt.Biology.Ecology.EvolutionaryFolkTheoremWanted
