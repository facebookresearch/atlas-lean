/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.SpectralExpander

/-!
# Spectral expanders: the Alon-Boppana bound and the expander Chernoff bound (wanted)

Two central facts about spectral expanders (S. Vadhan, *Pseudorandomness*, Foundations and Trends
in Theoretical Computer Science 7 (2012), Chapter 4), stated with the spectral-expander predicate
`IsSpectralExpander` and the random-walk probability `walkProb` of
`MathlibExt.Combinatorics.SimpleGraph.SpectralExpander`:

* the Alon-Boppana bound `λ ≥ 2 √(d - 1) / d - o(1)` (Theorem 4.11);
* the Chernoff bound for expander walks (Theorem 4.22).

The hitting property (Theorem 4.17) is proved in
`MathlibExt.Combinatorics.SimpleGraph.ExpanderWalk`.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.SpectralExpanderWanted

open MathlibExt.Combinatorics.SpectralExpander

/-- **Alon-Boppana bound.** Fix a degree `d`. For every `ε > 0` there is `N₀` such that every
`d`-regular graph on `n ≥ N₀` vertices that is a spectral expander with parameter `λ` has
`λ ≥ 2 √(d - 1) / d - ε`: the spectral parameter of large `d`-regular graphs is at least
`2 √(d - 1) / d - o(1)` as the number of vertices tends to infinity (S. Vadhan,
*Pseudorandomness* (2012), Theorem 4.11, stated there for multigraphs; this is the case of simple
graphs; due to Alon and Boppana, with a short proof by A. Nilli, Discrete Math. 91 (1991)). -/
theorem_wanted alon_boppana (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lam : ℝ),
      IsSpectralExpander G d lam → 2 * Real.sqrt ((d : ℝ) - 1) / d - ε ≤ lam

/-- **Chernoff bound for expander walks.** There is an absolute constant `C > 0` with the
following property. Let `G` be a `d`-regular graph, `d ≥ 1`, on a nonempty vertex set, that is a
spectral expander with parameter `λ`, let `f : V → [0, 1]` have mean `μ(f) = (1 / N) ∑_v f(v)`,
and let `V₀, …, V_t` be a random walk with `t` steps from a uniformly random start vertex. Then
for every `ε > 0`,
`Pr[|(1 / (t + 1)) ∑_{i ≤ t} f(Vᵢ) - μ(f)| ≥ λ + ε] ≤ 2 exp(-C ε² (t + 1))` (S. Vadhan,
*Pseudorandomness* (2012), Theorem 4.22, `2 e^{-Ω(ε² t)}` for a walk `V₁, …, V_t` of `t` vertices;
the bound is due to D. Gillman, SIAM J. Comput. 27 (1998)). -/
theorem_wanted chernoff_bound_expander_walk :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (d : ℕ) (lam : ℝ) (hG : IsSpectralExpander G d lam) (hd : 0 < d)
      (f : V → ℝ), (∀ v, 0 ≤ f v ∧ f v ≤ 1) → ∀ (t : ℕ) (ε : ℝ), 0 < ε →
        walkProb G d hG.1 hd t (fun w => lam + ε ≤
            |(1 / (t + 1 : ℝ)) * ∑ i, f (w i) - (1 / Fintype.card V : ℝ) * ∑ v, f v|) ≤
          2 * Real.exp (-(C * ε ^ 2 * (t + 1)))

end MathlibExt.GraphTheory.SpectralExpanderWanted
