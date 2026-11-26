/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Raft.Protocol

/-!
# Tests for the Raft consensus protocol

* Logs: `termAt` at index `0` and past the end, the up-to-date comparison (a later last term
  beats a longer log), and `mergeEntries` (a stale request truncates nothing, a conflict deletes
  the conflicting entry and all that follow it, missing entries are appended).
* Message handling: a vote goes to at most one candidate per term (a duplicate request is
  granted again), a newer term turns a leader into a follower, a stale AppendEntries request is
  refused, and Figure 2's rule for `commitIndex` can lower it on an old request.
* Non-vacuity: in a cluster of three servers, a run with a lost and a duplicated message in which
  server `0` is elected with the vote of server `1`, replicates the command `7` to it, commits it
  with the majority `{0, 1}`, and both servers apply it at index `1`.
* Crash and recovery: a server that voted in term `1`, then crashed and recovered, still refuses
  its vote to another candidate of term `1`.
* The single-server theorem for `Unit`.
-/

@[expose] public section

namespace Cslib.Distributed.Raft.Tests

open Cslib.Distributed.Raft

/-! ### Logs -/

example : termAt ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) 0 = 0 := rfl
example : termAt ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) 2 = 2 := rfl
example : termAt ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) 3 = 0 := rfl

/-- A shorter log with a later last term is more up to date. -/
example : AtLeastAsUpToDate 3 1 ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) := by decide
example : ¬ AtLeastAsUpToDate 2 1 ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) := by decide
example : AtLeastAsUpToDate 2 2 ([⟨1, 5⟩, ⟨2, 6⟩] : List (Entry ℕ)) := by decide
example : AtLeastAsUpToDate 0 0 ([] : List (Entry ℕ)) := by decide

/-- The consistency check: index `0` always passes; otherwise the entry must exist with that
term. -/
example : PrevMatches ([] : List (Entry ℕ)) 0 7 := by decide
example : PrevMatches ([⟨1, 5⟩] : List (Entry ℕ)) 1 1 := by decide
example : ¬ PrevMatches ([⟨1, 5⟩] : List (Entry ℕ)) 1 2 := by decide
example : ¬ PrevMatches ([⟨1, 5⟩] : List (Entry ℕ)) 2 1 := by decide

/-- A stale request whose entries are already present truncates nothing. -/
example : mergeEntries ([⟨1, 5⟩, ⟨1, 6⟩, ⟨2, 7⟩] : List (Entry ℕ)) [⟨1, 5⟩] =
    [⟨1, 5⟩, ⟨1, 6⟩, ⟨2, 7⟩] := rfl

/-- A conflict deletes the existing entry and all that follow it. -/
example : mergeEntries ([⟨1, 5⟩, ⟨2, 6⟩, ⟨2, 7⟩] : List (Entry ℕ)) [⟨1, 5⟩, ⟨3, 8⟩] =
    [⟨1, 5⟩, ⟨3, 8⟩] := rfl

/-- New entries beyond the end of the log are appended. -/
example : mergeEntries ([⟨1, 5⟩] : List (Entry ℕ)) [⟨1, 5⟩, ⟨1, 6⟩] = [⟨1, 5⟩, ⟨1, 6⟩] := rfl

/-! ### Message handling -/

/-- A follower of term `1` that voted for server `0`. -/
def voter : Server (Fin 3) ℕ := { (Server.init : Server (Fin 3) ℕ) with currentTerm := 1, votedFor := some 0 }

/-- A duplicate request of the candidate it voted for is granted again. -/
example : (voter.handle ⟨0, 1, .requestVote 1 0 0⟩).2 = {⟨1, 0, .requestVoteReply 1 true⟩} := by
  decide

/-- Another candidate of the same term is refused, and the vote stays with server `0`. -/
example : (voter.handle ⟨2, 1, .requestVote 1 5 1⟩).2 = {⟨1, 2, .requestVoteReply 1 false⟩} ∧
    (voter.handle ⟨2, 1, .requestVote 1 5 1⟩).1.votedFor = some 0 := by
  decide

/-- A candidate of a newer term gets the vote: the voter first moves to the new term. -/
example : (voter.handle ⟨2, 1, .requestVote 2 0 0⟩).1.votedFor = some 2 ∧
    (voter.handle ⟨2, 1, .requestVote 2 0 0⟩).1.currentTerm = 2 := by
  decide

/-- A leader of term `1` with log `[(1, 5)]`. -/
def leader : Server (Fin 3) ℕ :=
  { (Server.init : Server (Fin 3) ℕ) with currentTerm := 1, votedFor := some 0, role := .leader, log := [⟨1, 5⟩] }

/-- A response of a newer term turns a leader into a follower of that term. -/
example : (leader.handle ⟨1, 0, .appendEntriesReply 2 false 0⟩).1.role = .follower ∧
    (leader.handle ⟨1, 0, .appendEntriesReply 2 false 0⟩).1.currentTerm = 2 ∧
    (leader.handle ⟨1, 0, .appendEntriesReply 2 false 0⟩).1.votedFor = none := by
  decide

/-- A stale AppendEntries request is refused with the receiver's term. -/
example : (leader.handle ⟨2, 0, .appendEntries 0 0 0 [⟨0, 9⟩] 0⟩).2 =
    {⟨0, 2, .appendEntriesReply 1 false 0⟩} := by
  decide

/-- A follower of term `1` that knows its two entries to be committed. -/
def follower : Server (Fin 3) ℕ :=
  { (Server.init : Server (Fin 3) ℕ) with currentTerm := 1, log := [⟨1, 5⟩, ⟨1, 6⟩], commitIndex := 2 }

/-- Figure 2's rule `commitIndex := min(leaderCommit, index of last new entry)` lowers
`commitIndex` on an old request that matches only the first entry. -/
example : (follower.handle ⟨0, 1, .appendEntries 1 0 0 [⟨1, 5⟩] 3⟩).1.commitIndex = 1 ∧
    (follower.handle ⟨0, 1, .appendEntries 1 0 0 [⟨1, 5⟩] 3⟩).1.log = [⟨1, 5⟩, ⟨1, 6⟩] := by
  decide

/-! ### A run of three servers -/

/-- Receiving a message given by membership in the network. -/
theorem step_receive {s : State (Fin 3) ℕ} {m : Message (Fin 3) ℕ} (hm : m ∈ s.network)
    (hup : (s.server m.dst).up) :
    Step s (.receive m) ⟨Function.update s.server m.dst ((s.server m.dst).handle m).1,
      s.network.erase m + ((s.server m.dst).handle m).2⟩ :=
  Step.receive s m _ (Multiset.cons_erase hm).symm hup

/-- Losing a message given by membership in the network. -/
theorem step_drop {s : State (Fin 3) ℕ} {m : Message (Fin 3) ℕ} (hm : m ∈ s.network) :
    Step s (.drop m) { s with network := s.network.erase m } :=
  Step.drop s m _ (Multiset.cons_erase hm).symm

/-- The RequestVote request of server `0` in term `1`, to server `j`. -/
abbrev rv (j : Fin 3) : Message (Fin 3) ℕ := ⟨0, j, .requestVote 1 0 0⟩

/-- Server `1`'s vote for server `0` in term `1`. -/
abbrev vote : Message (Fin 3) ℕ := ⟨1, 0, .requestVoteReply 1 true⟩

/-- The AppendEntries request of leader `0` carrying its first entry to server `1`. -/
abbrev ae : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 0 0 [⟨1, 7⟩] 0⟩

/-- Server `1`'s acknowledgement of the first entry. -/
abbrev ack : Message (Fin 3) ℕ := ⟨1, 0, .appendEntriesReply 1 true 1⟩

/-- The heartbeat of leader `0` to server `1` after committing index `1`. -/
abbrev hb : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 1 1 [] 1⟩

/-- **Non-vacuity of the Raft model.** In a cluster of three servers, the RequestVote request to
server `2` is lost and the one to server `1` duplicated; server `1` grants its vote twice, server
`0` becomes leader of term `1`, takes the command `7`, replicates it to server `1`, commits it
with the majority `{0, 1}`, tells server `1` by a heartbeat, and both servers apply `7` at
index `1`. -/
theorem exists_run_three :
    ∃ s : State (Fin 3) ℕ, lts.MTr State.init
        [.timeout 0, .drop (rv 2), .duplicate (rv 1), .receive (rv 1), .receive (rv 1),
          .receive vote, .becomeLeader 0 1, .clientRequest 0 7, .appendEntries 0 1 1,
          .receive ae, .receive ack, .advanceCommitIndex 0 1, .apply 0 1 7,
          .appendEntries 0 1 0, .receive hb, .apply 1 1 7] s ∧
      (s.server 0).role = .leader ∧ (s.server 0).lastApplied = 1 ∧
      (s.server 1).role = .follower ∧ (s.server 1).log = [⟨1, 7⟩] ∧
      (s.server 1).commitIndex = 1 ∧ (s.server 1).lastApplied = 1 ∧
      (s.server 2).log = [] := by
  refine ⟨?s, ?run, ?props⟩
  case run =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_drop (m := rv 2) (by decide)) ?_
    refine .stepL (Step.duplicate _ (rv 1) (by decide)) ?_
    refine .stepL (step_receive (m := rv 1) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 1) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := vote) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 7 (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ae) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ack) (by decide) (by decide)) ?_
    refine .stepL (Step.advanceCommitIndex _ 0 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.apply _ 0 ⟨1, 7⟩ (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := hb) (by decide) (by decide)) ?_
    refine .stepL (Step.apply _ 1 ⟨1, 7⟩ (by decide) (by decide) (by decide)) ?_
    exact .refl
  case props => decide

/-! ### Crash and recovery -/

/-- **Votes survive crashes.** Server `1` votes for server `0` in term `1`, crashes and
recovers; it is a follower of term `1` that still has voted for `0`, and it refuses its vote to
server `2`, a candidate of term `1` with a longer log. -/
theorem exists_run_crash :
    ∃ s : State (Fin 3) ℕ, lts.MTr State.init
        [.timeout 0, .receive (rv 1), .crash 1, .recover 1] s ∧
      (s.server 1).up ∧ (s.server 1).role = .follower ∧ (s.server 1).currentTerm = 1 ∧
      (s.server 1).votedFor = some 0 ∧
      ((s.server 1).handle ⟨2, 1, .requestVote 1 3 1⟩).2 =
        {⟨1, 2, .requestVoteReply 1 false⟩} := by
  refine ⟨?s, ?run, ?props⟩
  case run =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 1) (by decide) (by decide)) ?_
    refine .stepL (Step.crash _ 1 (by decide)) ?_
    refine .stepL (Step.recover _ 1 (by decide)) ?_
    exact .refl
  case props => decide

/-! ### One server -/

example : ∃ s : State Unit ℕ, lts.MTr State.init
    [.timeout (), .becomeLeader () 1, .clientRequest () 7, .advanceCommitIndex () 1,
      .apply () 1 7] s ∧ (s.server ()).commitIndex = 1 :=
  let ⟨s, h, _, _, hc, _⟩ := exists_mTr_commit_of_subsingleton () (7 : ℕ)
  ⟨s, h, hc⟩

end Cslib.Distributed.Raft.Tests
