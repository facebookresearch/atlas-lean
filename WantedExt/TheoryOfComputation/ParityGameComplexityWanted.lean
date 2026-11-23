/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Parity games are in NP ∩ coNP, via progress-measure certificates
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Games.ProgressMeasure

@[expose] public section

namespace Cslib.ParityGameComplexityWanted

open Cslib.Games Cslib.Games.ProgressMeasure

/-!
# Parity games are in NP ∩ coNP, via progress-measure certificates

Deciding whether a position of a finite parity game is winning for the even
player is in NP ∩ coNP. The certificates are *small progress measures*
(Jurdziński): a map `μ` assigning to each position a tuple of length `d + 1`
(plus a top element `none`, for positions losing for the even player), such
that along every edge the tuple does not increase in the *truncated
lexicographic* order at the priority of the edge's tail, and strictly
decreases there when the priority is odd. The truncated order at priority
`p` compares the suffix `p, p + 1, …, d` lexicographically from the top
(largest priority) downwards: the first component where the two tuples
differ, scanning from `d` down to `p`, decides, and components below `p`
are ignored. In particular, components above `p` need not agree: a larger
higher component outweighs any difference below it. A progress measure
encodes a positional strategy (at an even position, the witness successor
gives the strategy's move), and it is checked by the costed verifier
`costedVerifyProgress`, which evaluates the truncated-lexicographic
comparisons and counts the atomic component comparisons it performs. The witness is
*small*: every component is at most `n`. For the odd player the same
verifier runs on the dual game (owners swapped, priorities incremented by
one), whose even winning region is the original game's odd winning region.

The games are encoded (`EncodedParityGame`: owner as a `Bool`, moves as a
`Bool` matrix, priorities as `ℕ → ℕ`), so the verifier is a concrete
computable function, not an existential Boolean. The verifier, its costed version and their proved
properties are in `CSLibExt.Computability.Games.ProgressMeasure`. The costed verifier
`costedVerifyProgress` returns the verifier's result together with the
number of atomic component comparisons it actually evaluates while
computing that result; proved theorems state that its result equals
`verifyProgress` and that its cost is at most
`verifyProgressCostBound n d`. Priority compression (replacing the
distinct priorities by values at most `2n` preserving order and parity,
`EncodedParityGame.priorityCompress`) makes the compressed game checkable
with `d = 2 * n`, so the check costs `O(n ^ 4)` in the number of
positions, and the compressed game has the same winning regions as the
original, since compression preserves the order and the parity of
priorities.
-/

/-- Source: E. A. Emerson and C. S. Jutla, "Tree automata, mu-calculus and
determinacy", *Proceedings of FOCS 1991*, 368-377 (positional determinacy and
the NP ∩ coNP bound); M. Jurdziński, "Small progress measures for solving
parity games", *Proceedings of STACS 2000*, LNCS 1770, 290-301 (the
polynomial-time checkable progress-measure certificate); W. Zielonka,
"Infinite games on finitely coloured graphs with applications to automata on
infinite trees", *Theoretical Computer Science* 200 (1998), 135-183. -/
public theorem_wanted parity_games_np_inter_coNP_wanted :
    ∀ {n d : ℕ} (G : EncodedParityGame n) (hser : ∀ v, ∃ w, G.move v w = true)
      (hbound : ∀ v, G.priority v ≤ d) (v : Fin n),
      (v ∈ (G.toParityGame hser).WinningRegion Player.even ↔
        ∃ μ : Fin n → Option (Fin (d + 1) → ℕ),
          (∀ u k, ∀ f, μ u = some f → f k ≤ n) ∧
            verifyProgress G μ = true ∧ ∃ f, μ v = some f) ∧
      (v ∈ (G.toParityGame hser).WinningRegion Player.odd ↔
        ∃ μ : Fin n → Option (Fin (d + 1 + 1) → ℕ),
          (∀ u k, ∀ f, μ u = some f → f k ≤ n) ∧
            verifyProgress G.dualGame μ = true ∧ ∃ f, μ v = some f) ∧
      (∀ μ : Fin n → Option (Fin (d + 1) → ℕ),
        (costedVerifyProgress G μ).1 = verifyProgress G μ ∧
          (costedVerifyProgress G μ).2 ≤ verifyProgressCostBound n d) ∧
      (∀ μ : Fin n → Option (Fin (d + 1 + 1) → ℕ),
        (costedVerifyProgress G.dualGame μ).1 = verifyProgress G.dualGame μ ∧
          (costedVerifyProgress G.dualGame μ).2 ≤
            verifyProgressCostBound n (d + 1)) ∧
      (v ∈ (G.toParityGame hser).WinningRegion Player.even ↔
        v ∈ (G.priorityCompress.toParityGame hser).WinningRegion Player.even) ∧
      (∀ μ : Fin n → Option (Fin (2 * n + 1) → ℕ),
        (costedVerifyProgress G.priorityCompress μ).2 ≤
          verifyProgressCostBound n (2 * n))

end Cslib.ParityGameComplexityWanted
