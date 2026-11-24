/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.GameTheory.BlackwellApproachabilityAlmostSure
public import MathlibExt.GameTheory.CorrelatedEquilibrium

@[expose] public section

/-! # Regret matching leads to correlated equilibria

Hart and Mas-Colell's *regret matching* (2000): each period a player switches from its last
action `j` to another action `k` with probability proportional to its regret for not having played
`k` whenever it played `j`, and otherwise repeats `j`. Their Main Theorem: when every player uses
it, the empirical distribution of play converges almost surely to the set of correlated
equilibria. The deterministic ingredients are proved in `MathlibExt`:
`CorrelatedEquilibrium.isCorrelatedEq_empirical_iff` (no conditional regret is the same as a
correlated approximate equilibrium, the Proposition of §3) and
`CorrelatedEquilibrium.sum_mul_sub_eq_zero_of_isRegretInvariant` (Blackwell's condition for
regret-invariant play, the core of Theorem A); the probabilistic convergence of the regrets is
recorded here.

## References

* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150: (2.1)–(2.3), footnote 5, Main Theorem (§2).
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430: §4, Theorem 1.
-/

namespace MathlibExt.GameTheory.RegretMatchingWanted

open MeasureTheory Filter Topology Finset
open MathlibExt.GameTheory.NoRegretDynamics (empirical)
open MathlibExt.GameTheory.CorrelatedEquilibrium (IsCorrelatedEq condRegret)
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma)

section RegretMatching

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- **Regret matching** (Hart and Mas-Colell 2000, (2.2), in cost form). After the history
`h` of the first `t + 1` rounds, let `j` be player `i`'s last action and
`R(j, k) = max(D(j, k), 0)` its regrets, where `D(j, k) = condRegret / (t + 1)` is the average
conditional regret (2.1b–c). Player `i` then plays each `k ≠ j` with probability `R(j, k) / μ`
and repeats `j` with the remaining probability. -/
noncomputable def regretMatching (cost : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ}
    (h : Fin (t + 1) → ∀ i, S i) (i : ι) (k : S i) : ℝ :=
  if k = h (Fin.last t) i then
    1 - ∑ l ∈ univ.erase (h (Fin.last t) i),
      max (condRegret cost h i (h (Fin.last t) i) l / (t + 1)) 0 / μ
  else max (condRegret cost h i (h (Fin.last t) i) k / (t + 1)) 0 / μ

/-- **Regret matching leads to correlated equilibria** (Hart and Mas-Colell 2000, Main Theorem;
Hart 2005, Theorem 1). Let `|cost i s| ≤ M` and `μ > 2 M (|Sᵢ| − 1)` for every player
(footnote 5). If the first round is arbitrary and, given the history of the first `t + 1`
rounds, the players choose the next round's actions independently, each according to regret
matching (2.2), then almost surely the empirical distributions of play (2.3) converge to the set
of correlated equilibria. -/
theorem_wanted regretMatching_tendsto_correlatedEq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (cost : ι → (∀ i, S i) → ℝ) {M μ : ℝ}
    (hM : ∀ i s, |cost i s| ≤ M) (hμ : ∀ i, 2 * M * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (X : ℕ → Ω → ∀ i, S i) (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : ∀ t s,
      P[{ω | X (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | historySigma X t] =ᵐ[P]
        fun ω => ∏ i, regretMatching cost μ (fun k : Fin (t + 1) => X k ω) i (s i)) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℕ => Metric.infDist
      (empirical (fun k : Fin (T + 1) => X k ω)) {ψ | IsCorrelatedEq cost ψ 0}) atTop (𝓝 0)

end RegretMatching

end MathlibExt.GameTheory.RegretMatchingWanted
