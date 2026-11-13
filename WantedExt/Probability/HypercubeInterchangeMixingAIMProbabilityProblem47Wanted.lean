/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mixing of the interchange process on the hypercube (AimPL Markov chain mixing times, Problem 4.2)

AimPL, Markov chain mixing times, Problem 4.2: obtain good bounds on the mixing time of the
interchange process on the hypercube `{0, 1}ⁿ`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
public import MathlibExt.Probability.MarkovMixing

@[expose] public section

namespace MathlibExt.Probability.HypercubeInterchangeMixingAIMProbabilityProblem47Wanted

/-!
Source: AimPL: Markov chain mixing times, Problem 4.2, http://aimpl.org/markovmixing/4/.
UnsolvedMath record UM-20002605 (`AIM-PROBABILITY-0047`), dataset ulamai/UnsolvedMath v1.8.0.

The interchange process is Hermon and Salez's: the continuous-time walk on permutations of the
vertices of `{0, 1}ⁿ` (MathlibExt's `SimpleGraph.hypercubeGraph n`) with generator `(L f)(σ) = ∑_{e
∈ E} (f(σ τ_e) - f(σ))` (unit edge rates, `τ_e` the transposition of the endpoints of `e`), started
at the identity; its law at time `t` is the identity row of `exp(t L)`. The mixing time is `min {t ≥
0 | d_TV ≤ 1/e}`, their convention. The answer is stated as the order of magnitude (`c n ≤ t_mix ≤ C
n` for `n ≥ 1`); sharper bounds are not determined by the source and are not formalized
(`partial_scope`).
-/

open MathlibExt.Probability.MarkovMixing

open Classical in
/-- The generator of the interchange process on the hypercube `Q_n` (MathlibExt's
`SimpleGraph.hypercubeGraph n`) with unit edge rates: from `σ` it jumps to `σ * swap x y` at
rate `1` for every edge `{x, y}` (the particles at `x` and `y` exchange positions), so
`L(σ, σ * swap x y) = 1` and `L(σ, σ) = -|E|`. Ordered adjacent pairs count each edge twice,
hence the factors `1/2`. -/
noncomputable def interchangeGenerator (n : ℕ) :
    Matrix (Equiv.Perm (Fin n → Bool)) (Equiv.Perm (Fin n → Bool)) ℝ :=
  fun σ τ =>
    (1 / 2 : ℝ) * ((Finset.univ.filter fun xy : (Fin n → Bool) × (Fin n → Bool) =>
        (SimpleGraph.hypercubeGraph n).Adj xy.1 xy.2 ∧ τ = σ * Equiv.swap xy.1 xy.2).card : ℝ) -
      if τ = σ then
        (1 / 2 : ℝ) * ((Finset.univ.filter fun xy : (Fin n → Bool) × (Fin n → Bool) =>
          (SimpleGraph.hypercubeGraph n).Adj xy.1 xy.2).card : ℝ)
      else 0

/-- The total variation distance at time `t` between the law `e^{tL}(id, ·)` of the interchange
process started at the identity and the uniform distribution on permutations of the vertices. -/
noncomputable def interchangeDistToUniform (n : ℕ) (t : ℝ) : ℝ :=
  tvDist (fun τ => (NormedSpace.exp (t • interchangeGenerator n)) 1 τ)
    (fun _ => 1 / (Fintype.card (Equiv.Perm (Fin n → Bool)) : ℝ))

/-- The total variation mixing time `min {t ≥ 0 | d(t) ≤ 1/e}` of the interchange process on the
`n`-dimensional hypercube (the convention of Hermon and Salez). -/
noncomputable def interchangeMixingTime (n : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ interchangeDistToUniform n t ≤ Real.exp (-1)}

/-- AimPL Markov chain mixing times, Problem 4.2, answered as a claim: the mixing time of the
unit-rate interchange process on the hypercube `{0, 1}ⁿ` is of order `n`: there are constants
`0 < c ≤ C` with `c n ≤ t_mix ≤ C n` for every `n ≥ 1`. -/
def hypercubeInterchangeMixingOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    c * n ≤ interchangeMixingTime n ∧ interchangeMixingTime n ≤ C * n

/--
Resolved: Hermon and Salez proved that the mixing time of the unit-rate interchange process on the
hypercube `{0, 1}ⁿ` is of order `n` (`t_mix ≍ log |V|` on product graphs of fixed side length),
resolving Wilson's conjecture recorded as this AIM problem. Source: AimPL: Markov chain mixing
times, Problem 4.2, http://aimpl.org/markovmixing/4/; resolution: J. Hermon and J. Salez, The
interchange process on high-dimensional products, Ann. Appl. Probab. 31 (2021), no. 1, 84-98,
arXiv:1905.02146, abstract and Corollary 2: every connected product graph of side length ℓ ≥ 2 has
t_mix^ip(G) ≍_ℓ log |V_G|, so the unit-rate interchange process on the hypercube {0,1}^n mixes in
time of order n, Wilson's conjecture, which the paper notes was reiterated as Problem 4.2 of the AIM
workshop; t_mix = min {t ≥ 0 : max_A |P(ξ_t ∈ A) - P(ξ* ∈ A)| ≤ 1/e},
https://doi.org/10.1214/20-AAP1583.
-/
public theorem_wanted hypercubeInterchangeMixingOrder_holds : hypercubeInterchangeMixingOrder

end MathlibExt.Probability.HypercubeInterchangeMixingAIMProbabilityProblem47Wanted
