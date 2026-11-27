/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The contact process on power-law random graphs has critical value zero

Chatterjee and Durrett (2009) consider the random graph of Newman, Strogatz and Watts on `n`
vertices: the degrees `d_1, …, d_n` are i.i.d. with law `P(d_i = k) = p_k`, conditioned on an
even sum; vertex `i` gets `d_i` half-edges, the half-edges are paired uniformly at random, and the
resulting multigraph is conditioned to be simple. On it runs the contact process: an infected
vertex recovers at rate `1`, and a healthy vertex becomes infected at rate `λ` times its number
of infected neighbours. Their Theorem 1: if `p_k ~ C k^(-α)` with `α > 3` and every degree is
at least `3`, then for every `λ > 0` there is `p(λ) > 0` such that, started from all vertices
infected, for every `δ > 0`, `inf_{t ≤ exp(n^(1-δ))} P(|ξ_t| / n ≥ p(λ)) → 1` as `n → ∞`: at
each time up to `exp(n^(1-δ))`, the infected fraction is at least `p(λ)` with probability tending
to `1`, uniformly in the time (probability over the graph and the process together). Hence the
critical value of the contact process on these graphs is `0`.

Given the degree sequence `d` of a simple graph `G`, the uniform pairing produces `G` in exactly
`∏ d_i!` of the `(2m - 1)!!` pairings of the `2m = ∑ d_i` half-edges, so the law above gives a
simple graph `G` mass proportional to `∏_i p_{d_i} d_i! / (2m - 1)!!` (`nswWeight`). The contact
process is the continuous-time Markov chain of
`MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`.

Sources: S. Chatterjee and R. Durrett, "Contact processes on random graphs with power law degree
distributions have critical value 0", Ann. Probab. 37 (2009) 2332–2356, Section 1 and
Theorem 1; M. E. J. Newman, S. H. Strogatz and D. J. Watts, "Random graphs with arbitrary
degree distributions and their applications", Phys. Rev. E 64 (2001) 026118.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace WantedExt.Biology.Epidemiology.PowerLawContactProcessWanted

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The total rate of a single transition `S → T` of the contact process on `G` with infection
rate `λ` and recovery rate `1`: `1` if `T = S \ {i}` for some `i ∈ S`, and
`λ · #{j ∈ S | j ~ i}` if `T = S ∪ {i}` for some `i ∉ S`. -/
noncomputable def jumpRate (G : SimpleGraph V) (lam : ℝ) (S T : Finset V) : ℝ :=
  ∑ i, ((if i ∈ S ∧ T = S.erase i then 1 else 0) +
    (if i ∉ S ∧ T = insert i S then lam * ((S.filter (G.Adj i)).card : ℝ) else 0))

/-- The rate matrix of the contact process on `G`: off the diagonal the single-transition rates,
and on the diagonal minus the total rate out of the state. It is a rate matrix
(`IsRateMatrix`) whenever `λ ≥ 0`. -/
noncomputable def contactRateMatrix (G : SimpleGraph V) (lam : ℝ) :
    Matrix (Finset V) (Finset V) ℝ :=
  fun S T => if T = S then -∑ U ∈ univ.erase S, jumpRate G lam S U else jumpRate G lam S T

open Classical in
/-- The unnormalized mass `∏_i p_{d_i} d_i! / (2m - 1)!!` that the Newman–Strogatz–Watts
construction gives a simple graph `G` with degrees `d_i` and `2m = ∑ d_i`. -/
noncomputable def nswWeight (p : ℕ → ℝ) (G : SimpleGraph V) : ℝ :=
  (∏ i, p (G.degree i) * ((G.degree i).factorial : ℝ)) /
    ((∑ i, G.degree i) - 1).doubleFactorial

/-- The normalized weight `nswWeight p G / ∑ H, nswWeight p H` of a simple graph `G` on `Fin n`
under the Newman–Strogatz–Watts model with degree law `p`. When the total weight
`∑ H : SimpleGraph (Fin n), nswWeight p H` is positive (i.e. admissible simple graphs exist for
`n` and `p`), this defines a probability law on `SimpleGraph (Fin n)` (otherwise Lean's `x / 0 = 0`
convention makes it identically zero). -/
noncomputable def nswLaw (p : ℕ → ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  nswWeight p G / ∑ H : SimpleGraph (Fin n), nswWeight p H

/-- The probability, over the random graph and the contact process together, that at time `t`
the contact process started from all `n` vertices infected has at least `q n` infected vertices.
When the total weight `∑ H, nswWeight p H` is `0` (for a degree law `p`, when no simple graph on
`Fin n` has all its degrees in the support of `p`), Lean's `x / 0 = 0` convention makes
`nswLaw p n` identically `0`, and then the value is `0` for every `t` and `q`. (`hQ` records that
each contact-process rate matrix is a rate matrix.) -/
noncomputable def annealedProb (p : ℕ → ℝ) (lam : ℝ)
    (hQ : ∀ n (G : SimpleGraph (Fin n)), IsRateMatrix (contactRateMatrix G lam)) (n : ℕ)
    (t : ℝ≥0) (q : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), nswLaw p n G *
    (ctmcInputMeasure (hQ n G)).real
      {ω | q * (n : ℝ) ≤ ((ctmcPath (contactRateMatrix G lam) univ ω t).card : ℝ)}

/-- **Chatterjee–Durrett theorem** (Chatterjee and Durrett 2009, Theorem 1). Let `p` be a degree
law on `ℕ` (`p_k ≥ 0`, `∑ p_k = 1`) with `p_0 = p_1 = p_2 = 0` (every degree at least `3`) and
`p_k / (C k^(-α)) → 1` as `k → ∞` for some `C > 0` and `α > 3`. Let `λ > 0`. Then there is
`q > 0` such that for every `δ > 0` and `ε > 0`, for all large `n` and all times
`0 ≤ t ≤ exp(n^(1-δ))`, the probability (over the Newman–Strogatz–Watts graph on `n` vertices
and the contact process started from all vertices infected) that at least `q n` vertices are
infected at time `t` is at least `1 - ε`. (`hQ` records that each contact-process rate matrix is
a rate matrix.) In particular the critical value of the contact process on these graphs is `0`.

Source: Chatterjee and Durrett (2009), Theorem 1. -/
theorem_wanted exists_pos_forall_annealedProb (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : HasSum p 1) (hdeg : p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0) (C α : ℝ) (hC : 0 < C)
    (hα : 3 < α) (hasymp : Tendsto (fun k : ℕ => p k / (C * (k : ℝ) ^ (-α))) atTop (𝓝 1))
    (lam : ℝ) (hlam : 0 < lam)
    (hQ : ∀ n (G : SimpleGraph (Fin n)), IsRateMatrix (contactRateMatrix G lam)) :
    ∃ q > 0, ∀ δ > 0, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0,
      (t : ℝ) ≤ Real.exp ((n : ℝ) ^ (1 - δ)) → 1 - ε ≤ annealedProb p lam hQ n t q

end WantedExt.Biology.Epidemiology.PowerLawContactProcessWanted
