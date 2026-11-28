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
  granted again), a newer term turns a leader into a follower, and a stale AppendEntries request
  is refused.
* Non-vacuity: in a cluster of three servers, a run with a lost and a duplicated message in which
  server `0` is elected with the vote of server `1`, replicates the command `7` to it, commits it
  with the majority `{0, 1}`, and both servers apply it at index `1`.
* Figure 2's update of a follower's `commitIndex`, taken literally, lowers it on fresh requests
  delivered in order, with nothing lost or duplicated, when they carry fewer entries than an
  earlier one: from `2` to `1`, then to `0` on a heartbeat sent while `nextIndex` lags.
* A leader keeps the larger `matchIndex` when acknowledgements arrive out of order, while
  `nextIndex` follows the last one.
* A leader re-elected in term `2` lowers `nextIndex` on a refusal of its term-`1` heartbeat, even
  though the follower's log agrees with its own.
* A conflicting entry is deleted: a server that recovers with an entry of term `1` replaces it by
  the entry of the leader of term `2`.
* Crash and recovery: after a server votes in term `1`, crashes and recovers, it still records
  its vote; given a term-`1` RequestVote from another candidate reporting a longer log, its
  handler would refuse.
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

/-! ### A run of three servers -/

/-- Receiving a message given by membership in the network: the message is in flight (`hm`) and
its receiver is up (`hup`). -/
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

/-! ### `commitIndex` can decrease on fresh requests -/

/-- Server `2`'s vote for server `0` in term `1`. -/
abbrev vote₂ : Message (Fin 3) ℕ := ⟨2, 0, .requestVoteReply 1 true⟩

/-- The three entries of leader `0` in term `1`. -/
abbrev es₃ : List (Entry ℕ) := [⟨1, 7⟩, ⟨1, 8⟩, ⟨1, 9⟩]

/-- Leader `0` replicating its three entries to server `2`. -/
abbrev ae₃ : Message (Fin 3) ℕ := ⟨0, 2, .appendEntries 1 0 0 es₃ 0⟩

/-- Server `2`'s acknowledgement of the three entries. -/
abbrev ack₃ : Message (Fin 3) ℕ := ⟨2, 0, .appendEntriesReply 1 true 3⟩

/-- Leader `0`, having committed index `3`, sends server `1` its first two entries... -/
abbrev reqY : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 0 0 [⟨1, 7⟩, ⟨1, 8⟩] 3⟩

/-- ...then its first entry... -/
abbrev reqX : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 0 0 [⟨1, 7⟩] 3⟩

/-- ...then a heartbeat, all with preceding index `0`, as `nextIndex 1` is still `1`. -/
abbrev reqH : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 0 0 [] 3⟩

/-- **`commitIndex` decreases on fresh requests.** Server `0` is elected with the vote of server
`2`, appends three entries, replicates them to server `2` and commits index `3`. It then sends
server `1` three fresh requests, with two entries, one entry and none, which arrive in order with
nothing lost or duplicated. Figure 2's update sets the `commitIndex` of server `1` to `2`, then
lowers it to `1`, then to `0`, while its log keeps both entries. -/
theorem exists_run_commitIndex_decreases :
    ∃ s₁ s₂ s₃ : State (Fin 3) ℕ,
      lts.MTr State.init
        [.timeout 0, .receive (rv 2), .receive vote₂, .becomeLeader 0 1, .clientRequest 0 7,
          .clientRequest 0 8, .clientRequest 0 9, .appendEntries 0 2 3, .receive ae₃,
          .receive ack₃, .advanceCommitIndex 0 3, .appendEntries 0 1 2, .appendEntries 0 1 1,
          .appendEntries 0 1 0, .receive reqY] s₁ ∧
      lts.MTr s₁ [.receive reqX] s₂ ∧ lts.MTr s₂ [.receive reqH] s₃ ∧
      (s₁.server 0).commitIndex = 3 ∧ (s₁.server 1).commitIndex = 2 ∧
      (s₂.server 1).commitIndex = 1 ∧ (s₃.server 1).commitIndex = 0 ∧
      (s₃.server 1).log = [⟨1, 7⟩, ⟨1, 8⟩] := by
  refine ⟨?s₁, ?s₂, ?s₃, ?run₁, ?run₂, ?run₃, ?props⟩
  case run₁ =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 2) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := vote₂) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 7 (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 8 (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 9 (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 2 3 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ae₃) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ack₃) (by decide) (by decide)) ?_
    refine .stepL (Step.advanceCommitIndex _ 0 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 2 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := reqY) (by decide) (by decide)) ?_
    exact .refl
  case run₂ =>
    refine .stepL (step_receive (m := reqX) (by decide) (by decide)) ?_
    exact .refl
  case run₃ =>
    refine .stepL (step_receive (m := reqH) (by decide) (by decide)) ?_
    exact .refl
  case props => decide

/-! ### Acknowledgements out of order -/

/-- Leader `0` sending server `2` its first entry. -/
abbrev ae₁ : Message (Fin 3) ℕ := ⟨0, 2, .appendEntries 1 0 0 [⟨1, 7⟩] 0⟩

/-- Server `2`'s acknowledgement of the first entry. -/
abbrev ack₁ : Message (Fin 3) ℕ := ⟨2, 0, .appendEntriesReply 1 true 1⟩

/-- **The leader keeps the larger `matchIndex`.** Leader `0` sends server `2` one entry, then
three; server `2` acknowledges both, and the acknowledgements arrive in the opposite order. The
leader's `matchIndex 2` stays `3`, the larger reported index, while `nextIndex 2` follows the last
acknowledgement to `2`. -/
theorem exists_run_matchIndex_max :
    ∃ s : State (Fin 3) ℕ, lts.MTr State.init
        [.timeout 0, .receive (rv 2), .receive vote₂, .becomeLeader 0 1, .clientRequest 0 7,
          .clientRequest 0 8, .clientRequest 0 9, .appendEntries 0 2 1, .appendEntries 0 2 3,
          .receive ae₁, .receive ae₃, .receive ack₃, .receive ack₁] s ∧
      (s.server 0).matchIndex 2 = 3 ∧ (s.server 0).nextIndex 2 = 2 ∧ (s.server 2).log = es₃ := by
  refine ⟨?s, ?run, ?props⟩
  case run =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 2) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := vote₂) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 7 (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 8 (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 9 (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 2 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 2 3 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ae₁) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ae₃) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ack₃) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ack₁) (by decide) (by decide)) ?_
    exact .refl
  case props => decide

/-! ### A refusal from an earlier term lowers `nextIndex` -/

/-- Leader `0`'s heartbeat to server `1` in term `1`, sent before the acknowledgement of `ae`. -/
abbrev hb₀ : Message (Fin 3) ℕ := ⟨0, 1, .appendEntries 1 0 0 [] 0⟩

/-- The RequestVote request of server `0` in term `2`, to server `1`. -/
abbrev rvT2 : Message (Fin 3) ℕ := ⟨0, 1, .requestVote 2 1 1⟩

/-- Server `1`'s vote for server `0` in term `2`. -/
abbrev voteT2 : Message (Fin 3) ℕ := ⟨1, 0, .requestVoteReply 2 true⟩

/-- Server `1`'s refusal of the term-`1` heartbeat, carrying its term `2`. -/
abbrev nack : Message (Fin 3) ℕ := ⟨1, 0, .appendEntriesReply 2 false 0⟩

/-- **A refusal of an earlier request lowers `nextIndex`.** Leader `0` of term `1` replicates its
entry to server `1` and also sends it a heartbeat, which is delayed. Server `0` crashes, recovers
and is elected again in term `2`, with `nextIndex 1 = 2`. Server `1` then refuses the old
heartbeat with its current term `2`, and leader `0` lowers `nextIndex 1` to `1`, although the two
logs agree. -/
theorem exists_run_stale_refusal :
    ∃ s : State (Fin 3) ℕ, lts.MTr State.init
        [.timeout 0, .receive (rv 1), .receive vote, .becomeLeader 0 1, .clientRequest 0 7,
          .appendEntries 0 1 1, .appendEntries 0 1 0, .receive ae, .receive ack, .crash 0,
          .recover 0, .timeout 0, .receive rvT2, .receive voteT2, .becomeLeader 0 2,
          .receive hb₀, .receive nack] s ∧
      (s.server 0).role = .leader ∧ (s.server 0).currentTerm = 2 ∧
      (s.server 0).nextIndex 1 = 1 ∧ (s.server 0).log = [⟨1, 7⟩] ∧
      (s.server 1).log = [⟨1, 7⟩] := by
  refine ⟨?s, ?run, ?props⟩
  case run =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 1) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := vote) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 7 (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.appendEntries _ 0 1 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ae) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := ack) (by decide) (by decide)) ?_
    refine .stepL (Step.crash _ 0 (by decide)) ?_
    refine .stepL (Step.recover _ 0 (by decide)) ?_
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rvT2) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := voteT2) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := hb₀) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := nack) (by decide) (by decide)) ?_
    exact .refl
  case props => decide

/-! ### A conflicting entry is deleted -/

/-- The RequestVote request of server `1` in term `2`, to server `2`. -/
abbrev rvB : Message (Fin 3) ℕ := ⟨1, 2, .requestVote 2 0 0⟩

/-- Server `2`'s vote for server `1` in term `2`. -/
abbrev voteB : Message (Fin 3) ℕ := ⟨2, 1, .requestVoteReply 2 true⟩

/-- Leader `1` of term `2` sending server `0` its entry. -/
abbrev aeB : Message (Fin 3) ℕ := ⟨1, 0, .appendEntries 2 0 0 [⟨2, 8⟩] 0⟩

/-- **A conflicting entry is deleted.** Leader `0` of term `1` appends the entry `(1, 7)` and
crashes before replicating it. Server `1` is elected in term `2` with the vote of server `2` and
appends `(2, 8)`. Server `0` recovers, receives that entry at index `1`, where its own entry has
a different term, and replaces its log by `[(2, 8)]`. -/
theorem exists_run_conflict :
    ∃ s : State (Fin 3) ℕ, lts.MTr State.init
        [.timeout 0, .receive (rv 1), .receive vote, .becomeLeader 0 1, .clientRequest 0 7,
          .crash 0, .timeout 1, .receive rvB, .receive voteB, .becomeLeader 1 2,
          .clientRequest 1 8, .recover 0, .appendEntries 1 0 1, .receive aeB] s ∧
      (s.server 0).log = [⟨2, 8⟩] ∧ (s.server 0).currentTerm = 2 ∧
      (s.server 0).role = .follower := by
  refine ⟨?s, ?run, ?props⟩
  case run =>
    refine .stepL (Step.timeout _ 0 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rv 1) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := vote) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 0 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 0 7 (by decide) (by decide)) ?_
    refine .stepL (Step.crash _ 0 (by decide)) ?_
    refine .stepL (Step.timeout _ 1 (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := rvB) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := voteB) (by decide) (by decide)) ?_
    refine .stepL (Step.becomeLeader _ 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (Step.clientRequest _ 1 8 (by decide) (by decide)) ?_
    refine .stepL (Step.recover _ 0 (by decide)) ?_
    refine .stepL (Step.appendEntries _ 1 0 1 (by decide) (by decide) (by decide)) ?_
    refine .stepL (step_receive (m := aeB) (by decide) (by decide)) ?_
    exact .refl
  case props => decide

/-! ### Crash and recovery -/

/-- **Votes survive crashes.** Server `1` votes for server `0` in term `1`, crashes and
recovers. After recovery, server `1` is a follower of term `1` and still records its vote for `0`.
If given a term-`1` RequestVote from `2` reporting a longer log (last index `3`, last term `1`),
its handler would refuse. -/
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
