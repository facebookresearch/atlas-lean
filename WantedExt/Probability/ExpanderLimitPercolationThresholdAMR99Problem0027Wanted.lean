/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Percolation thresholds along local limits of expanders (Benjamini, Open problem 5.10)

Benjamini, Coarse Geometry and Randomness, Open problem 5.10: show that if `{G_n}` is an expander
family and `G_n → G` with respect to the local metric `d_loc`, then `p_c(G_n) → p_c(G)`. The notes
present it as an easier case of Schramm's locality conjecture (Conjecture 5.9: `G_n → G` and
`p_c(G_n) < c < 1` imply `p_c(G_n) → p_c(G)`), noting that the expander condition implies `p_c(G_n)
< c` for some `c < 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Order.LiminfLimsup
public import MathlibExt.Combinatorics.SimpleGraph.VertexTransitive
public import MathlibExt.Probability.ProductBondPercolation

@[expose] public section

namespace MathlibExt.Probability.ExpanderLimitPercolationThresholdAMR99Problem0027Wanted

/-!
Source: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes 2011; Lecture Notes
in Mathematics 2100, Springer 2013), Open problem 5.10, PDF p. 40. UnsolvedMath record UM-10000027
(`AMR-099-0027`), dataset ulamai/UnsolvedMath v1.8.0.

Benjamini's Definition 1.8 defines expander families of finite `d`-regular graphs, but Section 5.2
uses the term for the infinite transitive graphs of Section 5.1: Open problem 5.10 is presented as a
case of Schramm's Conjecture 5.9 for transitive graphs, its finite-graph analogue is the notes'
Theorem 5.7 (Benjamini-Nachmias-Peres 2011, Theorem 1.3, already proved), and
Benjamini-Nachmias-Peres call Schramm's conjecture open 'even if we assume that they are uniformly
nonamenable'. So the graphs are infinite, connected, locally finite and vertex-transitive (the
UnsolvedMath record's finite-graph wording is not used), and convergence is Hutchcroft's: for every
`r`, eventually every `r`-ball of `G_n` is isomorphic to every `r`-ball of `G` by a root-preserving
isomorphism. 'Expander family' (a uniform positive Cheeger constant, i.e. uniform nonamenability) is
stated in Hutchcroft's spectral form `lim sup ρ(G_n) < 1` for the spectral radius `ρ` of simple
random walk: Hutchcroft calls a graph nonamenable when `ρ < 1` and writes 'uniformly nonamenable
graphs sequences (i.e., for sequences satisfying lim sup ρ(Gn) < 1)'; for the uniformly bounded
degrees forced by local convergence this is equivalent to a uniform Cheeger bound (discrete Cheeger
inequality). `p_c` is MathlibExt's bond-percolation threshold `criticalProb`.
-/

open Filter Topology

/-- The closed ball `B_G(v, r)` of radius `r` around `v` in the graph metric of `G`, as the induced
subgraph on `{w | dist(v, w) ≤ r}`. -/
abbrev ball {V : Type*} (G : SimpleGraph V) (v : V) (r : ℕ) :
    SimpleGraph {w : V // G.dist v w ≤ r} :=
  G.induce {w : V | G.dist v w ≤ r}

/-- Local convergence of graphs (Benjamini's `d_loc`, in the form Hutchcroft uses for transitive
graphs): for every `r` there is `N` such that for all `n ≥ N`, every vertex `vₙ` of `Gₙ` and every
vertex `v` of `G`, the ball of radius `r` around `vₙ` in `Gₙ` is isomorphic to the ball of radius
`r` around `v` in `G` by an isomorphism sending `vₙ` to `v`. -/
def ConvergesLocally {V : ℕ → Type*} (Gs : ∀ n, SimpleGraph (V n)) {W : Type*}
    (G : SimpleGraph W) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ (vn : V n) (v : W),
    ∃ e : ball (Gs n) vn r ≃g ball G v r, (e ⟨vn, by simp⟩ : W) = v

/-- The law of simple random walk on a locally finite graph started at `o` after `k` steps:
`walkProb G o k y` is the probability that the walk is at `y` at time `k`. -/
noncomputable def walkProb {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : V) : ℕ → V → ℝ
  | 0 => fun y => if y = o then 1 else 0
  | k + 1 => fun y => ∑ x ∈ G.neighborFinset y, walkProb G o k x / G.degree x

/-- The spectral radius `ρ(G) = lim sup_n p_{2n}(o, o)^{1/(2n)}` of simple random walk on `G`, seen
from the root `o` (for transitive graphs it does not depend on the root). -/
noncomputable def spectralRadius {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : V) : ℝ :=
  limsup (fun n : ℕ => walkProb G o (2 * n) o ^ ((1 : ℝ) / (2 * n))) atTop

/-- Benjamini, Open problem 5.10, in the form resolved by Hutchcroft: let `(Gₙ)` be a sequence of
infinite, connected, locally finite, vertex-transitive graphs that is uniformly nonamenable (an
expander family: `lim sup ρ(Gₙ) < 1`) and converges locally to an infinite, connected, locally
finite, vertex-transitive graph `G`; then the bond percolation thresholds converge,
`p_c(Gₙ) → p_c(G)`. -/
def expanderLimitPercolationThreshold : Prop :=
  ∀ (V : ℕ → Type) (Gs : ∀ n, SimpleGraph (V n)) [∀ n, DecidableEq (V n)]
    [∀ n, Countable (V n)] [∀ n, (Gs n).LocallyFinite]
    (W : Type) (G : SimpleGraph W) [Countable W] [G.LocallyFinite],
    (∀ n, Infinite (V n) ∧ (Gs n).Connected ∧ (Gs n).IsVertexTransitive) →
    Infinite W → G.Connected → G.IsVertexTransitive →
    (∃ c < 1, ∀ᶠ n in atTop, ∀ o : V n, spectralRadius (Gs n) o ≤ c) →
    ConvergesLocally Gs G →
    Tendsto (fun n => MathlibExt.Probability.ProductBondPercolation.criticalProb (Gs n)) atTop
      (𝓝 (MathlibExt.Probability.ProductBondPercolation.criticalProb G))

/--
Resolved true: for transitive graphs converging locally, a uniform exponential lower bound on growth
(in particular uniform nonamenability, `lim sup ρ(G_n) < 1`) implies `p_c(G_n) → p_c(G)`. Source: I.
Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes 2011; Lecture Notes in
Mathematics 2100, Springer 2013), Open problem 5.10, PDF p. 40; resolution: T. Hutchcroft, Locality
of the critical probability for transitive graphs of exponential growth, Ann. Probab. 48 (2020),
doi:10.1214/19-AOP1395; arXiv:1808.08940, Theorem 1.2: if transitive Gn converge locally to a
transitive G and lim inf gr(Gn) > 1, then pc(Gn) → pc(G); introduction (after Conjecture 1.1): 'The
result is new even in the case of uniformly nonamenable graphs sequences (i.e., for sequences
satisfying lim sup ρ(Gn) < 1)', using gr(G) ≥ ρ(G)^{-2} as quoted there,
https://arxiv.org/abs/1808.08940.
-/
public theorem_wanted expanderLimitPercolationThreshold_holds : expanderLimitPercolationThreshold

end MathlibExt.Probability.ExpanderLimitPercolationThresholdAMR99Problem0027Wanted
