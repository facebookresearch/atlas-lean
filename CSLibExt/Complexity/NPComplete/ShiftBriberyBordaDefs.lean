/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHIFT BRIBERY for Borda: definitions

Source:
E. Elkind, P. Faliszewski and A. Slinko, "Swap bribery", Algorithmic Game Theory (SAGT 2009),
Lecture Notes in Computer Science 5814, Springer (2009), 299-310,
doi:10.1007/978-3-642-04645-2_27 (arXiv:0905.3885), Definition 3.7 and Theorem 5.1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BordaManipulationTwoManipulatorsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda

open MetaMathlibExt.Complexity.NPComplete.BordaManipulationTwoManipulators (IsVote bordaScore)

/-- An instance: the number `m` of candidates, the preferred candidate `p`, one pair per voter
(its vote over `0, …, m - 1`, most preferred first, and its finite prices
`(ρ(1), …, ρ(j))`, `j` the index of `p` in the vote), and the budget `B`. -/
abbrev ShiftBriberyBordaInstance := ℕ × ℕ × List (List ℕ × List ℕ) × ℕ

/-- The voters of the instance, `Fin n` for `n` listed voters. -/
abbrev Voter (inst : ShiftBriberyBordaInstance) : Type := Fin inst.2.2.1.length

/-- The vote `v` after shifting `p` up by `k` places: `p` is removed and reinserted at index
`j - k`, where `j` is its index in `v`. -/
def shift (v : List ℕ) (p k : ℕ) : List ℕ :=
  (v.erase p).take (v.idxOf p - k) ++ p :: (v.erase p).drop (v.idxOf p - k)

/-- The price `ρ(k)` of shifting `p` up by `k ≤ j` places, with `ρ(0) = 0`. -/
def price (prices : List ℕ) (k : ℕ) : ℕ :=
  (0 :: prices).getD k 0

/-- Well-formedness of an instance: `p` is a candidate, and every voter's vote ranks the `m`
candidates and comes with one finite price per place `p` can move up, nondecreasing in the
shift. -/
def WellFormed (inst : ShiftBriberyBordaInstance) : Prop :=
  inst.2.1 < inst.1 ∧
    ∀ w ∈ inst.2.2.1, IsVote inst.1 w.1 ∧ w.2.length = w.1.idxOf inst.2.1 ∧
      w.2.Pairwise (· ≤ ·)

/-- Some shifts `kᵢ ≤ j`, of total price at most `B`, make `p` a Borda winner: no candidate scores
more than `p` in the bribed election. -/
def ShiftBriberyBordaFeasible (inst : ShiftBriberyBordaInstance) : Prop :=
  ∃ k : Voter inst → ℕ,
    (∀ i, k i ≤ (inst.2.2.1.get i).1.idxOf inst.2.1) ∧
      ∑ i, price (inst.2.2.1.get i).2 (k i) ≤ inst.2.2.2 ∧
      ∀ d < inst.1,
        bordaScore inst.1 (List.ofFn fun i => shift (inst.2.2.1.get i).1 inst.2.1 (k i)) d ≤
          bordaScore inst.1 (List.ofFn fun i => shift (inst.2.2.1.get i).1 inst.2.1 (k i))
            inst.2.1

open Classical in
/-- SHIFT BRIBERY for Borda as a decision problem over bitstrings. -/
noncomputable def shiftBriberyBordaDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShiftBriberyBordaInstance) x with
  | some i => decide (WellFormed i ∧ ShiftBriberyBordaFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShiftBriberyBorda
