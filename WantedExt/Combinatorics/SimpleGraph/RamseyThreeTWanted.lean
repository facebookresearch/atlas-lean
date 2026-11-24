/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# The Ramsey number `R(3, t)` has order `t² / log t`

Kim (1995) used a semi-random ("nibble") construction, analysed with martingale concentration,
to build triangle-free graphs on `n` vertices with independence number at most
`9 √(n log n)`. This gives `R(3, t) ≥ (1/162)(1 - o(1)) t² / log t`, and together with the upper
bound `R(3, t) ≤ (1 + o(1)) t² / log t` of Ajtai, Komlós and Szemerédi and Shearer it shows that
`R(3, t)` has order of magnitude `t² / log t`.

All statements use the repository's `SimpleGraph.graphRamsey`, the least `N` such that every
graph on `N` vertices contains a triangle or an independent set of size `t`.

Reference: J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random
Structures & Algorithms* 7 (1995), 173–207, Theorem 1.1, Corollary 1.2 and the discussion
following it (including equation (1)).
-/

@[expose] public section

open Filter Asymptotics SimpleGraph

namespace MathlibExt.Combinatorics.RamseyThreeTWanted

/-- **Kim's triangle-free graphs with small independence number.** Every sufficiently large
`n` has a triangle-free graph `G` on `n` vertices with `α(G) ≤ 9 √(n log n)`, logarithms
natural (J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random
Structures & Algorithms* 7 (1995), Theorem 1.1). -/
theorem_wanted exists_cliqueFree_three_indepNum_le :
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ (G.indepNum : ℝ) ≤ 9 * Real.sqrt (n * Real.log n)

/-- **Chromatic number of Kim's triangle-free graphs.** Every sufficiently large `n` has a
triangle-free graph `G` on `n` vertices with `χ(G) ≥ (1/9) √(n / log n)` (J. H. Kim, *Random
Structures & Algorithms* 7 (1995), Corollary 1.2, from `χ(G) ≥ n / α(G)`). -/
theorem_wanted exists_cliqueFree_three_chromaticNumber_ge :
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 3 ∧ ((1 : ℝ) / 9) * Real.sqrt (n / Real.log n) ≤ (G.chromaticNumber.toNat : ℝ)

/-- **Kim's lower bound for `R(3, t)`.** For every `ε > 0` and all sufficiently large `t`,
`R(3, t) ≥ (1 - ε) t² / (162 log t)`; that is, `R(3, t) ≥ c (1 - o(1)) t² / log t` with
`c = 1/162 = 1/(2 · 9²)` (J. H. Kim, *Random Structures & Algorithms* 7 (1995), the consequence
of Theorem 1.1 stated after Corollary 1.2). -/
theorem_wanted graphRamsey_three_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (1 - ε) * ((t : ℝ) ^ 2 / (162 * Real.log t)) ≤ (graphRamsey 3 t : ℝ)

/-- **Upper bound for `R(3, t)` (Ajtai–Komlós–Szemerédi, Shearer).** For every `ε > 0` and all
sufficiently large `t`, `R(3, t) ≤ (1 + ε) t² / log t` (J. B. Shearer, "A note on the
independence number of triangle-free graphs", *Discrete Math.* 46 (1983); as stated in J. H.
Kim, *Random Structures & Algorithms* 7 (1995), equation (1)). -/
theorem_wanted graphRamsey_three_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, (graphRamsey 3 t : ℝ) ≤ (1 + ε) * ((t : ℝ) ^ 2 / Real.log t)

/-- **`R(3, t)` has order of magnitude `t² / log t`.** `R(3, t) = Θ(t² / log t)` as `t → ∞`
(J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random Structures &
Algorithms* 7 (1995), abstract and Section 1: the lower bound after Corollary 1.2 together with
the upper bound (1)). -/
theorem_wanted graphRamsey_three_isTheta :
    (fun t : ℕ => (graphRamsey 3 t : ℝ)) =Θ[atTop] (fun t : ℕ => (t : ℝ) ^ 2 / Real.log t)

end MathlibExt.Combinatorics.RamseyThreeTWanted
