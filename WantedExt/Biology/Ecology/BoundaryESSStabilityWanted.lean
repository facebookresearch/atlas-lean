/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Every evolutionarily stable state is asymptotically stable for the replicator dynamics

For a symmetric matrix game with payoff matrix `A`, the replicator equation on the simplex
`Δ = {x | x ≥ 0, ∑ x = 1}` is `ẋ_i = x_i ((A x)_i - x · A x)`. Hofbauer, Schuster and Sigmund
(1979) showed that `p ∈ Δ` is an evolutionarily stable state (ESS, in the sense of Maynard Smith
and Price) iff `p · A x > x · A x` for all `x ≠ p` in `Δ` near `p`, so that
`V(x) = ∏ x_i ^ p_i` is a strict local Lyapunov function, and therefore every ESS, interior or on
the boundary of `Δ`, is asymptotically stable. An interior ESS attracts every interior orbit
(Hofbauer and Sigmund 2003, Theorem 7). Taylor and Jonker (1978) proved the stronger linear
statement for a regular ESS. The converse fails: the interior rest point of the four-member
hypercycle is asymptotically stable but not an ESS.

The related interior-ESS development lives in `Domains.Biology.Dynamics.ReplicatorStability`.
The global-attraction result `IsESS.tendsto_of_pos` is proved in
`Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos`, where `simplex`, `replicatorField`,
`IsReplicatorSolution` and `IsESS` are defined. The linear-stability result
`IsRegularESS.re_lt_zero` is proved in `Domains.Biology.Ecology.BoundaryESSStabilityReLtZero`,
where `replicatorJacobian` and `IsRegularESS` are defined. The local-superiority
characterization `isESS_iff_isLocallySuperior` is proved in
`Domains.Biology.Ecology.BoundaryESSStabilityIsESSIffIsLocallySuperior`, where
`IsLocallySuperior` is defined; this module states the remaining general boundary-ESS results.

Sources: J. Hofbauer, P. Schuster and K. Sigmund, "A note on evolutionary stable strategies and
game dynamics", J. Theor. Biol. 81 (1979) 609–612; P. D. Taylor and L. B. Jonker,
"Evolutionarily stable strategies and game dynamics", Math. Biosci. 40 (1978) 145–156, §§2–4;
J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bull. Amer. Math. Soc. (N.S.) 40
(2003) 479–519, §2.6, Theorem 7.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Complex.Basic
public import Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos
public import Domains.Biology.Ecology.BoundaryESSStabilityReLtZero
public import Domains.Biology.Ecology.BoundaryESSStabilityIsESSIffIsLocallySuperior

@[expose] public section

namespace WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

open Matrix Filter Topology

variable {ι : Type*} [Fintype ι]

/-- `p` is **asymptotically stable** for the replicator dynamics of `A` on `Δ`: `p ∈ Δ`; every
state of `Δ` has a forward solution; `p` is Lyapunov stable (for every `ε > 0` there is `δ > 0` such
that every solution starting in `Δ` within `δ` of `p` stays within `ε` of `p` for all `t ≥ 0`);
and `p` is locally attracting (there is `δ > 0` such that every solution starting in `Δ` within
`δ` of `p` converges to `p`). -/
def IsAsymptoticallyStable (A : Matrix ι ι ℝ) (p : ι → ℝ) : Prop :=
  p ∈ simplex ι ∧
  (∀ x₀ ∈ simplex ι, ∃ x : ℝ → ι → ℝ, x 0 = x₀ ∧ IsReplicatorSolution A x) ∧
  (∀ ε > 0, ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x → x 0 ∈ simplex ι →
      ‖x 0 - p‖ < δ → ∀ t, 0 ≤ t → ‖x t - p‖ < ε) ∧
  ∃ δ > 0, ∀ x : ℝ → ι → ℝ, IsReplicatorSolution A x → x 0 ∈ simplex ι →
    ‖x 0 - p‖ < δ → Tendsto x atTop (𝓝 p)

/-- **Every ESS is asymptotically stable** (Hofbauer, Schuster and Sigmund 1979). For every
payoff matrix `A` and every ESS `p` of `A`, interior or on the boundary of `Δ`, `p` is
asymptotically stable for the replicator dynamics: `p ∈ Δ`, solutions from `Δ` exist, `p` is
Lyapunov stable on `Δ`, and `p` attracts every solution starting in `Δ` near `p`.

Source: Hofbauer, Schuster and Sigmund (1979), corollary after D4. -/
public theorem_wanted IsESS.isAsymptoticallyStable {A : Matrix ι ι ℝ} {p : ι → ℝ}
    (h : IsESS A p) : IsAsymptoticallyStable A p

/-- The payoff matrix of the **four-member hypercycle** with rates `k`:
`a_{i, i-1} = k_i` (indices mod 4) and all other entries `0`. -/
def hypercycle (k : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if j = i - 1 then k i else 0

/-- **The converse fails** (Hofbauer, Schuster and Sigmund 1979, hypercycle example). For every
`k` with `k i > 0` for all `i`, the four-member hypercycle has a rest point `p` with `p i > 0`
for all `i` and `∑ p = 1` that is asymptotically stable for the replicator dynamics but is not
an ESS.

Source: Hofbauer, Schuster and Sigmund (1979), p. 611. -/
public theorem_wanted hypercycle_not_isESS (k : Fin 4 → ℝ) (hk : ∀ i, 0 < k i) :
    ∃ p : Fin 4 → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ replicatorField (hypercycle k) p = 0 ∧
      IsAsymptoticallyStable (hypercycle k) p ∧ ¬ IsESS (hypercycle k) p

end WantedExt.Biology.Ecology.BoundaryESSStabilityWanted
