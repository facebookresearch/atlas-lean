/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FILE TRANSFER SCHEDULING is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Fintype.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FileTransferScheduling

/-!
# FILE TRANSFER SCHEDULING is NP-complete

INSTANCE: a file transfer graph, i.e., an undirected multigraph `G = (V, E)`, a port constraint
function `p : V → Z⁺` and a file length function `L : E → Z⁺`, and a positive integer `K`.
QUESTION: is there a file transfer schedule `s : E → N` (file `e` is transferred during the time
interval `[s(e), s(e) + L(e))`, without interruption) such that at every time `t` and at every
vertex `v` at most `p(v)` of the files incident to `v` are being transferred, and the makespan
`max_{e ∈ E} (s(e) + L(e))` is at most `K`?

Coffman, Garey, Johnson and LaPaugh introduce the problem (vertices are computer centers with
`p(v)` communication ports, edges are files to transfer between their endpoints, and "once the
transfer of a file begins it continues without interruption", as Nakano and Nishizeki restate
the model) and show the general problem NP-complete. Membership in NP: the schedule `s` is the
certificate (only the at most `2|E|` start and end times need checking).

The multigraph is a list of files `(u, v, L(e))` on the vertices `0, …, n - 1`; repeated pairs
are parallel edges (several files between the same two centers), and the endpoints are distinct.
A file of length `L(e)` started at `s(e)` occupies the `L(e)` unit time slots
`s(e), …, s(e) + L(e) - 1`, so it finishes at `s(e) + L(e)`, the quantity in the makespan
(Crescenzi and Kann print the closed interval `s(e) ≤ t ≤ s(e) + L(e)` in the port condition;
the half-open interval is the one consistent with their makespan). Start times are natural
numbers, as in Crescenzi and Kann.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FILE TRANSFER SCHEDULING is NP-complete.** Source: Coffman, Garey, Johnson and LaPaugh
(1985); Crescenzi and Kann, MINIMUM FILE TRANSFER SCHEDULING. -/
public theorem_wanted fileTransferScheduling_npComplete :
    fileTransferSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fileTransferSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.FileTransferScheduling
