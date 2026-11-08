/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleSequenceAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.MultipleSequenceAlignment

/-!
# Multiple sequence alignment tests

Closed checks with match `2`, mismatch `-1`, gap `-1`: two sequences `[true]`
aligned by one column score `2`, and the induced pairwise alignment of a
two-column MSA. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def msaTestScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

/-- Two sequences `[true]`, aligned in a single column. -/
def msaTestSeqs : Fin 2 → List Bool := fun i => [true]

/-- The single-column alignment of the two `[true]` sequences. -/
def msaTestAlign : MSAlignment 2 Bool := [fun _ => some true]

example : IsMSAlignment msaTestSeqs msaTestAlign := by
  refine ⟨fun col hc => ?_, fun i => ?_⟩
  · simp only [msaTestAlign, List.mem_singleton] at hc
    rw [hc]
    exact ⟨0, by simp⟩
  · rfl

example : msaScore msaTestScore (-1) msaTestAlign = 2 := by decide

example : inducedPair msaTestAlign 0 1 = [(some true, some true)] := by decide

example (σ : Bool → Bool → ℤ) {k : ℕ} {seqs : Fin k → List Bool}
    {A : MSAlignment k Bool} (hA : IsMSAlignment seqs A) (i j : Fin k) :
    IsAlignment (inducedPair A i j) (seqs i) (seqs j) :=
  inducedPair_isAlignment hA i j

example (σ : Bool → Bool → ℤ) {k : ℕ} {A : MSAlignment k Bool} :
    msaScore σ (-1) A =
      ∑ p ∈ pairFinset k, alignmentScore σ (-1) (inducedPair A p.1 p.2) :=
  msaScore_eq_sum_induced σ (-1)

example (σ : Bool → Bool → ℤ) {k : ℕ} {seqs : Fin k → List Bool}
    {A : MSAlignment k Bool} (hA : IsMSAlignment seqs A) :
    msaScore σ (-1) A ≤
      ∑ p ∈ pairFinset k, nwScore σ (-1) (seqs p.1) (seqs p.2) :=
  msaScore_le_sum_nwScore σ (-1) hA

example (k : ℕ) (seqs : Fin k → List Bool) : ∃ A, IsMSAlignment seqs A :=
  exists_isMSAlignment (∑ i, (seqs i).length) seqs le_rfl

#print axioms inducedPair_isAlignment
#print axioms msaScore_eq_sum_induced
#print axioms msaScore_le_sum_nwScore
#print axioms exists_isMSAlignment

end Cslib.Algorithms.Lean
