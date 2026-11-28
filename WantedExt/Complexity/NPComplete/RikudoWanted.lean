/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RIKUDO is NP-complete

Source:
V.-H. Nguyen and K. Perrot, "Rikudo is NP-complete", Theoretical Computer Science 910 (2022),
34-47, doi:10.1016/j.tcs.2022.01.034 (arXiv:2101.09332).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RikudoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Rikudo

/-!
# RIKUDO is NP-complete

Nguyen and Perrot (2022), Section 2: "Let us consider the hexagonal grid with pointy orientation,
and denote `C` the set of cells. Given a subset `τ ⊂ C`, we associate the loopless graph `G_τ`
on vertex set `τ` with adjacency relation corresponding to pairs of cells sharing an edge. We
say that `τ` is connected whenever `G_τ` is connected. A Rikudo game is a connected finite
subset of cells `τ` and, with `n = |τ|` and `[n] = {1, ..., n}`,
* a partial injective map `m : τ → [n]` (numbers already placed),
* a subset of the adjacency relation `p` (given adjacencies).
A solution is a bijective map `s : τ → [n]` such that, with symmetric binary relation `↔_s` on
`C` defined as `c ↔_s c' ⟺ |s(c) − s(c')| = 1`,
* `↔_s` is contained in the adjacency relation (the sequence of numbers forms a Hamiltonian
  path in `G_τ`),
* `s(c) = m(c)` for all cells `c` in the domain of `m` (respect given numbers),
* `p ⊆ ↔_s` (respect given adjacencies)."
RIKUDO asks whether a game admits a solution; Theorem 1 shows it NP-hard ("both problems are
trivially in NP").

Cells are given in axial coordinates of the pointy hexagonal grid: in `ℤ²`, cell `(q, r)` shares
an edge with exactly the six cells `(q ± 1, r)`, `(q, r ± 1)`, `(q + 1, r - 1)` and
`(q - 1, r + 1)`. Every finite instance can be translated into non-negative coordinates, which
preserves adjacency, so cells are pairs of natural numbers and `HexAdj` compares them in `ℤ²`.
The map `s` is a function on cells whose restriction to `τ` is a bijection onto `{1, ..., n}`;
`↔_s ⊆` adjacency is stated as: cells of `τ` with consecutive numbers share an edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RIKUDO is NP-complete.** Source: Nguyen and Perrot (2022), Theorem 1. -/
public theorem_wanted rikudo_npComplete :
    rikudoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rikudoDec

end MetaMathlibExt.Complexity.NPComplete.Rikudo
