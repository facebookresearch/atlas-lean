/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs
import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVotersDefs
import CSLibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVotersDefs
import CSLibExt.Complexity.NPComplete.CopelandManipulationTwoManipulatorsDefs
import CSLibExt.Complexity.NPComplete.IteratedWeakDominanceDefs
import CSLibExt.Complexity.NPComplete.PointToPointConnectionDefs

/-! # Feasibility and index bounds

Each decision problem checks well-formedness before accepting. These examples distinguish
that check from a universal quantifier in the raw feasibility predicate.
-/

namespace MetaMathlibExt.Complexity.NPComplete

open MetaMathlibExt.BitstringEncoding (bitEncode bitDecode_bitEncode)

namespace CondorcetConstructiveControlByAddingVoters

private abbrev outside : CondorcetConstructiveControlByAddingVotersInstance :=
  (2, [[0, 1]], [[1, 0]], 2, 1)

example : CondorcetConstructiveControlByAddingVotersFeasible outside ∧
    condorcetConstructiveControlByAddingVotersDec (bitEncode outside) = false := by
  constructor
  · refine ⟨[], by decide, by decide, ?_⟩
    intro a _ ha
    exact False.elim ((Nat.ne_of_lt a.isLt) ha)
  · have h : ¬ WellFormed outside := by unfold WellFormed; decide
    simp [condorcetConstructiveControlByAddingVotersDec, bitDecode_bitEncode, h]

end CondorcetConstructiveControlByAddingVoters

namespace CondorcetConstructiveControlByDeletingVoters

private abbrev outside : CondorcetConstructiveControlByDeletingVotersInstance :=
  (2, [[0, 1]], 2, 1)

example : CondorcetConstructiveControlByDeletingVotersFeasible outside ∧
    condorcetConstructiveControlByDeletingVotersDec (bitEncode outside) = false := by
  constructor
  · refine ⟨[[0, 1]], by decide, by decide, ?_⟩
    intro a _ ha
    exact False.elim ((Nat.ne_of_lt a.isLt) ha)
  · have h : ¬ WellFormed outside := by unfold WellFormed; decide
    simp [condorcetConstructiveControlByDeletingVotersDec, bitDecode_bitEncode, h]

end CondorcetConstructiveControlByDeletingVoters

namespace CopelandConstructiveControlByAddingVoters

private abbrev outside :
    CondorcetConstructiveControlByAddingVoters.CondorcetConstructiveControlByAddingVotersInstance :=
  (2, [[0, 1]], [[1, 0]], 2, 1)

example (α : ℚ) : CopelandConstructiveControlByAddingVotersFeasible α outside ∧
    copelandConstructiveControlByAddingVotersDec α (bitEncode outside) = false := by
  constructor
  · refine ⟨[], by decide, by decide, ?_⟩
    intro a _ ha
    exact False.elim ((Nat.ne_of_lt a.isLt) ha)
  · have h : ¬ WellFormed outside := by unfold WellFormed; decide
    simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, h]

end CopelandConstructiveControlByAddingVoters

namespace CopelandManipulationTwoManipulators

private abbrev outside : BordaManipulationTwoManipulators.BordaManipulationInstance :=
  (2, [[0, 1]], 2)

example (α : ℚ) : CopelandManipulationFeasible α outside ∧
    copelandManipulationDec α (bitEncode outside) = false := by
  constructor
  · have hv : BordaManipulationTwoManipulators.IsVote 2 [0, 1] := List.Perm.refl _
    refine ⟨[0, 1], [0, 1], hv, hv, ?_⟩
    intro a _ ha
    exact False.elim ((Nat.ne_of_lt a.isLt) ha)
  · have h : ¬ BordaManipulationTwoManipulators.WellFormed outside := by
      unfold BordaManipulationTwoManipulators.WellFormed BordaManipulationTwoManipulators.IsVote
      decide
    simp [copelandManipulationDec, bitDecode_bitEncode, h]

end CopelandManipulationTwoManipulators

namespace IteratedWeakDominance

private abbrev outside : IteratedWeakDominanceInstance :=
  (1, 1, [[((0, 0), (0, 0))]], true, 1)

example : IteratedWeakDominanceFeasible outside ∧
    iteratedWeakDominanceDec (bitEncode outside) = false := by
  constructor
  · refine ⟨(Finset.univ, Finset.univ), .refl, ?_⟩
    change ∀ c ∈ (Finset.univ : Finset (Fin 1)), (c : ℕ) ≠ 1
    exact fun c _ => Nat.ne_of_lt c.isLt
  · have h : ¬ WellFormed outside := by unfold WellFormed; decide
    simp [iteratedWeakDominanceDec, bitDecode_bitEncode, h]

end IteratedWeakDominance

namespace PointToPointConnection

private abbrev outside : PointToPointConnectionInstance := (2, [], [(0, 2), (2, 0)], 1)

example : PointToPointConnectionFeasible outside ∧
    pointToPointConnectionDec (bitEncode outside) = false := by
  constructor
  · refine ⟨[], by decide, by decide, ?_⟩
    intro q hq hs hd
    change q ∈ [(0, 2), (2, 0)] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd hd (by decide)
    · exact absurd hs (by decide)
  · have h : ¬ WellFormed outside := by unfold WellFormed; decide
    simp [pointToPointConnectionDec, bitDecode_bitEncode, h]

end PointToPointConnection

end MetaMathlibExt.Complexity.NPComplete
