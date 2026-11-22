/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Geography is PSPACE-complete

Source:
T. J. Schaefer, "On the complexity of some two-person perfect-information games", Journal of
Computer and System Sciences 16 (1978), 185-225.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GeographyPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Geography is PSPACE-complete

Geography, the two-player game of moving a token along directed edges without revisiting
vertices, is `PSPACE`-complete: the first player has a winning strategy exactly for the
`PSPACE`-complete language. `GeoWins` alternates players: a position is winning when there is a
move to a position from which the opponent cannot win. The start vertex is marked visited at
the outset, so a path never repeats a vertex; edge endpoints and the start are required below
`n`. The instance decodes to `(n, edges, start)`.
-/


/-- Winning positions in Geography, by recursion on the fuel (at most `n` moves remain). -/
def GeoWins : ℕ → List (ℕ × ℕ) → ℕ → List ℕ → Prop
  | 0, _, _, _ => False
  | fuel + 1, edges, pos, visited =>
    ∃ nxt, (pos, nxt) ∈ edges ∧ nxt ∉ visited ∧ ¬ GeoWins fuel edges nxt (nxt :: visited)

open Classical in
/-- Geography as a decision problem over bitstrings. -/
noncomputable def geographyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × ℕ) x with
  | some i => decide (i.2.2 < i.1 ∧
      (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1) ∧
      GeoWins (i.1 + 1) i.2.1 i.2.2 [i.2.2])
  | none => false

/-- **Geography is PSPACE-complete.** Source: T. J. Schaefer, "On the complexity of some two-
person perfect-information games", Journal of Computer and System Sciences 16 (1978),
185-225. -/
public theorem_wanted geography_pspace_complete :
    geographyDec ∈ PSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L geographyDec

end MetaMathlibExt.Complexity.KeyTheorems.GeographyPSPACEComplete
