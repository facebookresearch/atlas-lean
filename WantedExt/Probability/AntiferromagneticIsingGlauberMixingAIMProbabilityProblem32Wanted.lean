/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Optimal mixing for the antiferromagnetic Ising model up to uniqueness (AimPL Markov mixing, 1.3)

AimPL, Markov chain mixing times, Problem 1.3: take a (random) `d`-regular graph and the
antiferromagnetic Ising model (`J_{ij} = -1`). Can we show fast mixing `O(n log n)` up to `(d - 1)
tanh(β) < 1`? The list notes that this is known in the ferromagnetic case (Mossel-Sly).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Probability.MarkovMixing

@[expose] public section

namespace MathlibExt.Probability.AntiferromagneticIsingGlauberMixingAIMProbabilityProblem32Wanted

/-!
Source: AimPL: Markov chain mixing times, Problem 1.3, http://aimpl.org/markovmixing/1/.
UnsolvedMath record UM-20002590 (`AIM-PROBABILITY-0032`), dataset ulamai/UnsolvedMath v1.8.0.

The model is the zero-field Ising model with coupling `J = -1` at inverse temperature `β > 0`: `μ(σ)
∝ exp(-β ∑_{uv ∈ E} σ_u σ_v)` on spins `±1`, and the chain is the Glauber (heat-bath) dynamics, as
in Chen, Liu and Vigoda. Mixing is the `1/4` convention (MathlibExt's `IsMixedAt`, their convention)
at time `⌈C n log n⌉`, `C` depending on `d` and `β`. The statement covers every `d`-regular graph,
not only random ones. Convention (a pure reparametrization): Chen, Liu and Vigoda weight a
configuration by `b^{m(σ)}`, `m(σ)` the number of monochromatic edges; since `∑_{uv ∈ E} σ_u σ_v = 2
m(σ) - |E|`, the model here is theirs with `b = e^{-2β}` and no field (`λ = 1`); `β > 0` is `b < 1`,
and `(d - 1) tanh β < 1` is `b > (d - 2)/d`, their antiferromagnetic tree uniqueness threshold
`β_c(d)`.
-/

open MathlibExt.Probability.MarkovMixing

/-- The Gibbs weight `exp(β ∑_{uv ∈ E} J σ_u σ_v)` with `J = -1` (zero-field antiferromagnetic Ising
model at inverse temperature `β`) of the spin configuration `σ` on `G`, spins `±1` given by
`sgn`; each edge is counted once. -/
noncomputable def isingWeight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : ℝ)
    (σ : Fin n → Bool) : ℝ :=
  Real.exp (-β * ((1 / 2) * ∑ u, ∑ v, if G.Adj u v then sgn (σ u) * sgn (σ v) else 0))

/-- The Gibbs distribution `μ(σ) = w(σ) / ∑_τ w(τ)`. -/
noncomputable def isingGibbs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : ℝ)
    (σ : Fin n → Bool) : ℝ :=
  isingWeight G β σ / ∑ τ, isingWeight G β τ

/-- The transition matrix of the Glauber (heat-bath) dynamics: pick a uniform vertex `v` and
resample the spin at `v` from the Gibbs distribution given the other spins, so
`P(σ, τ) = (1/n) ∑_v [τ = σ off v] w(τ) / (w(τ) + w(τ with the spin at v flipped))`. -/
noncomputable def glauberMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (β : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℝ :=
  fun σ τ => (1 / n : ℝ) * ∑ v, if ∀ u, u ≠ v → τ u = σ u then
    isingWeight G β τ / (isingWeight G β τ + isingWeight G β (Function.update τ v (!τ v)))
    else 0

/-- AimPL Markov chain mixing times, Problem 1.3, as a claim: for `d ≥ 3` and `β > 0` with
`(d - 1) tanh β < 1`, the Glauber dynamics of the zero-field antiferromagnetic Ising model at
inverse temperature `β` mixes in `O(n log n)` steps on every `n`-vertex `d`-regular graph: some `C`
has `1/4`-mixing at time `⌈C n log n⌉`. -/
def antiferromagneticIsingFastMixing : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ β : ℝ, 0 < β → (d - 1 : ℝ) * Real.tanh β < 1 →
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsRegularOfDegree d →
      IsMixedAt (glauberMatrix G β) (isingGibbs G β) ⌈C * n * Real.log n⌉₊

/--
Resolved true: Chen, Liu and Vigoda proved `O(n log n)` mixing of Glauber dynamics for the Ising
model on all graphs of maximum degree `Δ` whenever their edge weight `b` lies strictly between `(Δ -
2)/Δ` and `Δ/(Δ - 2)` (tree uniqueness); with `b = e^{-2β}` and no field, the zero-field
antiferromagnetic model at `β > 0` is in this region exactly when `(d - 1) tanh β < 1`. Source:
AimPL: Markov chain mixing times, Problem 1.3, http://aimpl.org/markovmixing/1/; resolution: Z.
Chen, K. Liu and E. Vigoda, Optimal mixing of Glauber dynamics: entropy factorization via
high-dimensional expansion, Proceedings of the 53rd Annual ACM SIGACT Symposium on Theory of
Computing (STOC 2021), 1537-1550, arXiv:2011.02075, Theorem 1.4: for all Δ ≥ 3 and δ ∈ (0, 1) there
is C = C(Δ, δ) such that for every n-vertex graph of maximum degree at most Δ, every β ∈
[(Δ-2+δ)/(Δ-δ), (Δ-δ)/(Δ-2+δ)] (weight β^{m(σ)}, m the number of monochromatic edges) and every
field λ > 0, Glauber dynamics for the Ising model mixes in at most C n log n steps; the tree
uniqueness threshold of the antiferromagnetic Ising model is β_c(Δ) = (Δ-2)/Δ, and the paper notes
that the theorem yields optimal mixing whenever β is between (Δ-2)/Δ and Δ/(Δ-2),
https://doi.org/10.1145/3406325.3451035.
-/
public theorem_wanted antiferromagneticIsingFastMixing_holds : antiferromagneticIsingFastMixing

end MathlibExt.Probability.AntiferromagneticIsingGlauberMixingAIMProbabilityProblem32Wanted
