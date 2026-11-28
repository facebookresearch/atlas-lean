/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHIFT BRIBERY for Borda is NP-complete

Source:
E. Elkind, P. Faliszewski and A. Slinko, "Swap bribery", Algorithmic Game Theory (SAGT 2009),
Lecture Notes in Computer Science 5814, Springer (2009), 299-310,
doi:10.1007/978-3-642-04645-2_27 (arXiv:0905.3885), Definition 3.7 and Theorem 5.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ShiftBriberyBordaDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda

open MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators (IsVote bordaScore)

/-!
# SHIFT BRIBERY for Borda is NP-complete

INSTANCE: an election `E = (C, V)` with candidates `C = {c₁, …, cₘ}`, a preferred candidate
`p ∈ C`, and voters `V = (v₁, …, vₙ)`, each a strict linear order over `C`; for each voter `vᵢ` a
shift-bribery price function `ρᵢ : ℕ → ℕ ∪ {+∞}`, i.e., if `p` appears in the `j`-th position of
`vᵢ`, then `ρᵢ(0) = 0`, `ρᵢ(k) ≤ ρᵢ(k')` for `k < k' < j`, and `ρᵢ(k) = +∞` for `k ≥ j`; and a
nonnegative integer `B` (the budget). QUESTION: is there a sequence `(k₁, …, kₙ)` of nonnegative
integers such that `∑ᵢ ρᵢ(kᵢ) ≤ B` and bribing each voter `vᵢ` to shift `p` up by `kᵢ` places
ensures that `p` is a Borda winner of the resulting election?

Under Borda each voter gives each candidate as many points as the number of candidates it ranks
below that candidate, and every candidate with the highest total score is a winner (Elkind,
Faliszewski and Slinko use the nonunique-winner model). Scores reuse `bordaScore` of
`WantedExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsWanted` (the candidate at
position `i`, counting from `1`, of a vote over `m` candidates gets `m - i` points), and votes are
its `IsVote`: the candidates are `0, …, m - 1`, a vote lists all of them, most preferred first.
Shifting `p` up by `k` places in a vote where `p` has index `j` (counting from `0`) removes `p`
and reinserts it at index `j - k`; the `k` candidates it passes move down by one place. The finite
prices `ρᵢ(1), …, ρᵢ(j)` (with `j` the index of `p`, counting from `0`) are listed per voter,
`ρᵢ(0) = 0`, and the infinite prices are expressed by allowing only shifts `kᵢ ≤ j`. Numbers use
the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SHIFT BRIBERY for Borda is NP-complete.** Source: Elkind, Faliszewski and Slinko (2009),
Theorem 5.1. -/
public theorem_wanted shiftBriberyBorda_npComplete :
    shiftBriberyBordaDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shiftBriberyBordaDec

end MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda
