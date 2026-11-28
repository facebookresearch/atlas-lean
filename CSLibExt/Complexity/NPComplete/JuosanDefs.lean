/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.HeyawakeDefs

/-!
# JUOSAN: definitions

Juosan is played on a rectangular grid of cells divided into rectangular territories; each
territory contains a number or no number. Every cell is filled with a `−`-mark or a `|`-mark so
that (Iwamoto and Ibusuki, Section 1):
1. "The number in a territory shows the number of `−`-marks if `−`-marks have majority, or the
   number of `|`-marks if `|`-marks have majority. However, there are also cases where the
   numbers of `−`-marks and `|`-marks are the same. Territories with no numbers may have any
   number of `−`-marks and `|`-marks."
2. "`−`-marks can extend across more than three cells horizontally, but not more than two cells
   vertically."
3. "`|`-marks can extend across more than three cells vertically, but not more than two cells
   horizontally."

INSTANCE: a rectangular grid of cells divided into rectangular territories, each with a number
or no number. QUESTION: is there a solution? (Theorem 1: the Juosan puzzle problem is
NP-complete.)

Rule 1 says that the number is the larger of the two counts (with a tie, both counts equal
it). Rules 2 and 3 forbid three vertically consecutive `−`-marks and three horizontally
consecutive `|`-marks.

The grid is given explicitly, as in `HeyawakeDefs`, whose
instance, `rows`, `cols`, `roomOf` and `WellFormed` are reused: entry `c` of row `r` is the
index of the territory (Heyawake's room) containing cell `(r, c)`, and territory `k` carries
`(numbered, number)`; `WellFormed` requires a nonempty grid with rows of equal length,
territory indices in range, and every territory nonempty and rectangular. A filling is a
function `ℕ → ℕ → Bool` read on the grid, `true` for a `−`-mark and `false` for a `|`-mark.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
C. Iwamoto and T. Ibusuki, "Polynomial-time reductions from 3SAT to Kurotto and Juosan puzzles",
IEICE Transactions on Information and Systems E103-D(3) (2020), 500-505,
doi:10.1587/transinf.2019FCP0004 (Section 1: the rules and the decision problem; Theorem 1).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Juosan

open MetaMathlibExt.Complexity.NPComplete.Heyawake (HeyawakeInstance rows cols roomOf WellFormed)

/-- The number of cells of territory `k` whose mark is `b` under the filling `m`. -/
def markCount (i : HeyawakeInstance) (m : ℕ → ℕ → Bool) (k : ℕ) (b : Bool) : ℕ :=
  ((Finset.range (rows i) ×ˢ Finset.range (cols i)).filter
    fun x => roomOf i x.1 x.2 = k ∧ m x.1 x.2 = b).card

/-- The filling `m` (`true` = `−`, `false` = `|`) satisfies the three rules. -/
def Solves (i : HeyawakeInstance) (m : ℕ → ℕ → Bool) : Prop :=
  -- 1. a numbered territory's number is the larger of its two mark counts
  (∀ k < i.2.length, (i.2.getD k (false, 0)).1 = true →
    (i.2.getD k (false, 0)).2 = max (markCount i m k true) (markCount i m k false)) ∧
  -- 2. no `−`-mark run covers three cells vertically
  (∀ r c, r + 2 < rows i → c < cols i →
    ¬ (m r c = true ∧ m (r + 1) c = true ∧ m (r + 2) c = true)) ∧
  -- 3. no `|`-mark run covers three cells horizontally
  (∀ r c, r < rows i → c + 2 < cols i →
    ¬ (m r c = false ∧ m r (c + 1) = false ∧ m r (c + 2) = false))

/-- Some filling satisfies the rules. -/
def JuosanFeasible (i : HeyawakeInstance) : Prop :=
  ∃ m : ℕ → ℕ → Bool, Solves i m

open Classical in
/-- JUOSAN as a decision problem over bitstrings. -/
noncomputable def juosanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HeyawakeInstance) x with
  | some i => decide (WellFormed i ∧ JuosanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Juosan
