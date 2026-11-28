/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOOD-IT is NP-complete

Source:
R. Clifford, M. Jalsenius, A. Montanaro, and B. Sach, "The complexity of flood filling games",
Theory of Computing Systems 50(1) (2012), 72-92, doi:10.1007/s00224-011-9339-2
(arXiv:1001.4420, Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FloodItDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FloodIt

/-!
# FLOOD-IT is NP-complete

For a fixed number of colors `c ≥ 3`:

INSTANCE: an `n × n` board of tiles, each allocated one of `c` colors, and an integer `k`.
QUESTION: can the board be made a single color with at most `k` flooding operations? A flooding
operation chooses a color `a` and changes the color of every tile of the monochromatic region
connected to the top left tile to `a`.

Tiles are `Fin n × Fin n` (row, column), adjacent when left/right/up/down neighbors, i.e. in
Mathlib's grid graph `pathGraph n □ pathGraph n` (`Grid`). Two adjacent tiles of the same color
are connected (`SameColorGraph`), and the region of the top left tile `(0, 0)` is the set of
tiles reachable from it in that graph (`Region`). `flood col a` recolors that region with `a`;
after it, neighboring regions already of color `a` join the region, which the next operation
sees through `Region` of the new coloring. The colors are `0, …, c - 1`, and the board is given
row by row as a list of `n²` colors.

Clifford, Jalsenius, Montanaro and Sach prove that for every `c ≥ 3` the decision version of
`c`-Flood-It is NP-complete (Theorem 1), so the statement is quantified over `c ≥ 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FLOOD-IT is NP-complete for every fixed number of colors `c ≥ 3`.** Source: Clifford,
Jalsenius, Montanaro, and Sach (2012), Theorem 1. -/
public theorem_wanted floodIt_npComplete (c : ℕ) (_hc : 3 ≤ c) :
    floodItDec c ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (floodItDec c)

end MetaMathlibExt.Complexity.NPComplete.FloodIt
