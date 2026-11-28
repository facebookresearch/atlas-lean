/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# FLOOD-IT: definitions

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

Source:
R. Clifford, M. Jalsenius, A. Montanaro, and B. Sach, "The complexity of flood filling games",
Theory of Computing Systems 50(1) (2012), 72-92, doi:10.1007/s00224-011-9339-2
(arXiv:1001.4420, Theorem 1).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FloodIt

/-- An instance: the side length `n`, the colors of the board row by row (the tile in row `r`
and column `s` has the color at index `r * n + s`), and the move bound `k`. -/
abbrev FloodItInstance := ℕ × List ℕ × ℕ

/-- The `n × n` grid graph: tiles `(r, s)`, adjacent when they share a side. -/
abbrev Grid (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n

/-- Adjacent tiles of the same color under the coloring `col`. -/
def SameColorGraph {n : ℕ} (col : Fin n × Fin n → ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.fromRel fun x y => (Grid n).Adj x y ∧ col x = col y

/-- The tile `x` is in the monochromatic region connected to the top left tile `(0, 0)`. -/
def Region {n : ℕ} (col : Fin n × Fin n → ℕ) (x : Fin n × Fin n) : Prop :=
  ∃ t : Fin n × Fin n, (t.1 : ℕ) = 0 ∧ (t.2 : ℕ) = 0 ∧ (SameColorGraph col).Reachable t x

open Classical in
/-- The flooding operation with color `a`: the region of the top left tile gets color `a`. -/
noncomputable def flood {n : ℕ} (col : Fin n × Fin n → ℕ) (a : ℕ) : Fin n × Fin n → ℕ :=
  fun x => if Region col x then a else col x

/-- The initial coloring of the board. -/
def board (i : FloodItInstance) : Fin i.1 × Fin i.1 → ℕ :=
  fun x => i.2.1.getD (x.1 * i.1 + x.2) 0

/-- Well-formedness of an instance for `c` colors: the board is nonempty, has `n²` tiles, and
every tile has one of the colors `0, …, c - 1`. -/
def WellFormed (c : ℕ) (i : FloodItInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 * i.1 ∧ ∀ a ∈ i.2.1, a < c

/-- Some sequence of at most `k` flooding operations, each with one of the `c` colors, leaves
every tile with the same color. -/
def FloodItFeasible (c : ℕ) (i : FloodItInstance) : Prop :=
  ∃ moves : List ℕ, moves.length ≤ i.2.2 ∧ (∀ a ∈ moves, a < c) ∧
    ∀ x y, moves.foldl flood (board i) x = moves.foldl flood (board i) y

open Classical in
/-- FLOOD-IT with `c` colors as a decision problem over bitstrings. -/
noncomputable def floodItDec (c : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FloodItInstance) x with
  | some i => decide (WellFormed c i ∧ FloodItFeasible c i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FloodIt
