/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.ExpanderChernoff

/-!
# The Alon-Boppana bound for spectral expanders (wanted)

The Alon-Boppana bound for spectral expanders is Theorem 4.11 of S. Vadhan, *Pseudorandomness*,
Foundations and Trends in Theoretical Computer Science 7 (2012).
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

end MathlibExt.GraphTheory.SpectralExpanderWanted
