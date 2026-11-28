/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FILE TRANSFER SCHEDULING: definitions

Source:
E. G. Coffman, Jr., M. R. Garey, D. S. Johnson and A. S. LaPaugh, "Scheduling file transfers",
SIAM Journal on Computing 14(3) (1985), 744-780, doi:10.1137/0214054;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM FILE TRANSFER SCHEDULING (the decision version of the optimization problem stated here);
S. Nakano and T. Nishizeki, "Scheduling file transfers under port and channel constraints",
ISA '91 Algorithms, Lecture Notes in Computer Science 557 (1991), 43-51,
doi:10.1007/3-540-54945-5_48, Section 1 (restating the model of Coffman et al.).
-/
module

public import Mathlib.Data.Fintype.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FileTransferScheduling

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), files `(u, v, L(e))`, port
constraints `p(0), …, p(n - 1)`, and the makespan bound `K`. -/
abbrev FileTransferSchedulingInstance := ℕ × List (ℕ × ℕ × ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance: every file joins two distinct vertices and has positive
length, there is one positive port constraint per vertex, and `0 < K`. -/
def WellFormed (i : FileTransferSchedulingInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2) ∧
    i.2.2.1.length = i.1 ∧ (∀ x ∈ i.2.2.1, 0 < x) ∧ 0 < i.2.2.2

/-- A schedule with makespan at most `K`: start times `s e` for the files (indexed by their
positions in the list) such that every file ends by `K` and, at every vertex `v` and every time
`t`, at most `p(v)` files incident to `v` are in transfer at `t`. -/
def FileTransferSchedulingFeasible (i : FileTransferSchedulingInstance) : Prop :=
  ∃ s : Fin i.2.1.length → ℕ, (∀ e, s e + i.2.1[e].2.2 ≤ i.2.2.2) ∧
    ∀ v < i.1, ∀ t : ℕ,
      (Finset.univ.filter fun e : Fin i.2.1.length =>
          (i.2.1[e].1 = v ∨ i.2.1[e].2.1 = v) ∧ s e ≤ t ∧ t < s e + i.2.1[e].2.2).card ≤
        i.2.2.1.getD v 0

open Classical in
/-- FILE TRANSFER SCHEDULING as a decision problem over bitstrings. -/
noncomputable def fileTransferSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FileTransferSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ FileTransferSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FileTransferScheduling
