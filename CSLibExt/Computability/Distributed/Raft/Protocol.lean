/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Data.Fintype.Card

/-!
# The Raft consensus protocol

The Raft protocol of D. Ongaro and J. Ousterhout, *In search of an understandable consensus
algorithm*, USENIX ATC 2014, as summarised in their Figure 2, without cluster membership changes
or log compaction: a CSLib labelled transition system (`Cslib.LTS`) on the states of a cluster
and of the network that connects its servers.

**Model.**

* *Servers:* a fixed finite type `S` of servers; a majority is a set of more than half of them.
* *Synchrony:* none. Events interleave in any order. Timers are abstracted away: an election
  timeout is an event that may happen at any moment at a follower or a candidate that is up.
* *Failures:* a server fails by stopping (`crash`) and loses its volatile state; it may later
  recover (`recover`) as a follower with its persistent state, `currentTerm`, `votedFor` and its
  log. Steps are atomic, so persistent state reaches stable storage before any reply is sent.
* *Messages:* the network is a multiset of messages in flight. Any message in flight may be
  received next, provided its receiver is up, or much later (reordering, delay); the network may
  lose a message (`drop`) or duplicate one (`duplicate`) whether or not its receiver is up.
  Messages are not corrupted.
* *Clients:* a client request is an event that hands an arbitrary command to a leader. Replies
  to clients and the redirection of clients are not modelled.
* *State machines:* applying an entry is the event `apply i n c`, server `i` applying the command
  `c` of its entry at index `n`; the state machine itself is not modelled.

Responses carry their sender and, for AppendEntries, the index of the last entry matched, which
stand in for the context of a remote procedure call. After the rule for a newer term, a response
is acted on only by a candidate (a vote) or a leader (an AppendEntries response) whose current
term it carries, and a leader ignores AppendEntries requests of its own term. Without that
context, a leader re-elected in a later term may act on a refusal of one of its requests of an
earlier term, which carries the responder's current term, and lower `nextIndex`. On success a
leader takes the larger of `matchIndex` and the reported match index. A leader may send any number
of consecutive entries from `nextIndex` on.

Figure 2's update of a follower's `commitIndex` to `min(leaderCommit, p + |entries|)` is taken
literally, the index of the last new entry being read as the preceding index `p` for a request
with no entries. It lowers `commitIndex` on any accepted request whose leader commit exceeds
`commitIndex` but whose match index is below it: an old or duplicated request, or a fresh one with
fewer entries, such as a heartbeat sent while `nextIndex` lags.

**Main definitions.** `Server`, `Message`, `State`, `State.init`, `Server.handle` (how a server
handles a message), `Step` and `lts`.

**Results.** `currentTerm_le_of_mTr`: terms never decrease. `votedFor_eq_of_mTr`: a server's vote
in a term never changes, across crashes included. `exists_mTr_commit_of_subsingleton`: a
single-server cluster elects itself, commits a client command and applies it.
-/

@[expose] public section

namespace Cslib.Distributed.Raft

variable {S C : Type*}

/- **Raft log entry.** An entry of a Raft log holds a command for the state machine and the term
in which the leader received it. -/
structure Entry (C : Type*) where
  /-- The term in which the leader received the entry. -/
  term : ℕ
  /-- The command for the state machine. -/
  cmd : C
deriving DecidableEq

/- **Roles of a Raft server.** A Raft server is a follower, a candidate or a leader. -/
inductive Role
  /-- Responds to requests from candidates and leaders. -/
  | follower
  /-- Seeks votes to become leader. -/
  | candidate
  /-- Takes client commands and replicates its log. -/
  | leader
deriving DecidableEq

/- **Term of a Raft log entry by index.** For a log `l`, indexed from `1`, `termAt l n` is the
term of its entry at index `n`, and `0` when `n = 0` or `l` has no entry at index `n`. -/
def termAt (l : List (Entry C)) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (l[n]?.map Entry.term).getD 0

/- **Raft's up-to-date comparison of logs** (Ongaro and Ousterhout, Section 5.4.1). A log whose
last entry has term `t` and index `n` is at least as up to date as the log `l` when `t` is larger
than the term of the last entry of `l`, or the two terms are equal and `n` is at least the length
of `l`. An empty log has last index and last term `0`. -/
def AtLeastAsUpToDate (t n : ℕ) (l : List (Entry C)) : Prop :=
  termAt l l.length < t ∨ (t = termAt l l.length ∧ l.length ≤ n)

instance (t n : ℕ) (l : List (Entry C)) : Decidable (AtLeastAsUpToDate t n l) :=
  inferInstanceAs (Decidable (_ ∨ _))

/- **Raft's AppendEntries consistency check.** A log `l` passes the check for the preceding
index `n` and the preceding term `t` when `n = 0`, or `l` has an entry at index `n` and its term
is `t`. -/
def PrevMatches (l : List (Entry C)) (n t : ℕ) : Prop :=
  n = 0 ∨ (n ≤ l.length ∧ termAt l n = t)

instance (l : List (Entry C)) (n t : ℕ) : Decidable (PrevMatches l n t) :=
  inferInstanceAs (Decidable (_ ∨ _))

/- **Merging new entries into a Raft log** (AppendEntries, steps 3 and 4). `mergeEntries l es`
puts the new entries `es` in the places of the existing entries `l`, both starting just after the
preceding index. At the first new entry whose existing counterpart has a different term, the
existing entry and all that follow it are deleted and the remaining new entries appended. New
entries that are already present (same index and term) leave the existing entry in place, as do
existing entries beyond the last new one when none of them conflicts. -/
def mergeEntries : List (Entry C) → List (Entry C) → List (Entry C)
  | l, [] => l
  | [], es => es
  | x :: l, e :: es => if x.term = e.term then x :: mergeEntries l es else e :: es

/- **State of a Raft server** (Ongaro and Ousterhout, Figure 2). Whether the server is up; its
persistent state, which survives crashes: the latest term `currentTerm` it has seen, the server
`votedFor` that received its vote in the current term, if any, and its `log`, indexed from `1`;
and its volatile state, lost in a crash: its `role`, the index `commitIndex` of the highest entry
known to be committed, the index `lastApplied` of the highest entry applied to its state
machine, and, used when it is a leader, for each server the index `nextIndex` of the next entry
to send to it and the index `matchIndex` of the highest entry known to be replicated on it, and,
used when it is a candidate, the set `votesGranted` of the servers that granted it their vote in
its current term. -/
structure Server (S C : Type*) where
  /-- Whether the server is up. -/
  up : Bool
  /-- The latest term the server has seen (persistent). -/
  currentTerm : ℕ
  /-- The server that received this server's vote in its current term, if any (persistent). -/
  votedFor : Option S
  /-- The log; its entry at index `n ≥ 1` is `log[n - 1]` (persistent). -/
  log : List (Entry C)
  /-- Follower, candidate or leader (volatile). -/
  role : Role
  /-- The index of the highest log entry known to be committed (volatile). -/
  commitIndex : ℕ
  /-- The index of the highest log entry applied to the state machine (volatile). -/
  lastApplied : ℕ
  /-- For each server, the index of the next log entry to send to it, used by a leader
  (volatile). -/
  nextIndex : S → ℕ
  /-- For each server, the index of the highest log entry known to be replicated on it, used by a
  leader (volatile). -/
  matchIndex : S → ℕ
  /-- The servers that granted this server their vote in its current term, used by a candidate
  (volatile). -/
  votesGranted : Finset S

namespace Server

/- **Initial state of a Raft server.** The server is up, in term `0`, has voted for no one and has
an empty log; it is a follower with `commitIndex` and `lastApplied` equal to `0`, every
`nextIndex` equal to `1`, every `matchIndex` equal to `0`, and no votes. -/
def init : Server S C where
  up := true
  currentTerm := 0
  votedFor := none
  log := []
  role := .follower
  commitIndex := 0
  lastApplied := 0
  nextIndex := fun _ => 1
  matchIndex := fun _ => 0
  votesGranted := ∅

/- **A Raft server crashes.** It stops and keeps its persistent state, `currentTerm`, `votedFor`
and `log`; its volatile state takes its initial values. -/
def crash (sv : Server S C) : Server S C :=
  { (init : Server S C) with
    up := false, currentTerm := sv.currentTerm, votedFor := sv.votedFor, log := sv.log }

/- **Raft's rule for a newer term** (Ongaro and Ousterhout, Figure 2, rules for all servers). A
server that sees a term `t` larger than its `currentTerm` sets `currentTerm` to `t`, forgets its
vote and becomes a follower; otherwise it is unchanged. -/
def observeTerm (sv : Server S C) (t : ℕ) : Server S C :=
  if sv.currentTerm < t then { sv with currentTerm := t, votedFor := none, role := .follower }
  else sv

end Server

/- **Contents of a Raft message** (Ongaro and Ousterhout, Figure 2): the RequestVote and
AppendEntries requests and their responses. A successful AppendEntries response also carries the
index of the last entry it matched. -/
inductive Payload (C : Type*)
  /-- A RequestVote request: the candidate's term and the index and term of its last log
  entry. -/
  | requestVote (term lastLogIndex lastLogTerm : ℕ)
  /-- A RequestVote response: the responder's current term and whether it granted its vote. -/
  | requestVoteReply (term : ℕ) (voteGranted : Bool)
  /-- An AppendEntries request: the leader's term, the index and term of the entry preceding the
  new entries, the new entries and the leader's `commitIndex`. -/
  | appendEntries (term prevLogIndex prevLogTerm : ℕ) (entries : List (Entry C))
      (leaderCommit : ℕ)
  /-- An AppendEntries response: the responder's current term, whether it accepted the entries
  and, on success, the index of the last entry it matched (`0` on failure). -/
  | appendEntriesReply (term : ℕ) (success : Bool) (matchIndex : ℕ)
deriving DecidableEq

/- **Term carried by a Raft message.** Every request and response carries a term, the current
term of its sender when the protocol sends it; `Payload.term` reads it off. -/
def Payload.term : Payload C → ℕ
  | .requestVote t _ _ | .requestVoteReply t _ | .appendEntries t _ _ _ _
  | .appendEntriesReply t _ _ => t

/- **Raft message.** A message from the server `src` to the server `dst` with contents
`payload`. The sender of a request is the candidate or leader that issues it. -/
structure Message (S C : Type*) where
  /-- The sender. -/
  src : S
  /-- The receiver. -/
  dst : S
  /-- The contents. -/
  payload : Payload C
deriving DecidableEq

/- **State of a Raft cluster.** The state of each server and the multiset of messages in
flight. -/
structure State (S C : Type*) where
  /-- The state of each server. -/
  server : S → Server S C
  /-- The messages in flight, with multiplicity. -/
  network : Multiset (Message S C)

/- **Initial state of a Raft cluster.** Every server is in its initial state and no message is
in flight. -/
def State.init : State S C := ⟨fun _ => .init, 0⟩

/- **Events of the Raft protocol**, the labels of its transition system: the election timeout of
a server, its election as leader of a term, a client request to a leader, an AppendEntries request
with at most `k` entries sent by a leader, a leader advancing its `commitIndex`, a server applying
the command of the entry at an index, the receipt of a message, the loss or the duplication of a
message by the network, and the crash and the recovery of a server. -/
inductive Event (S C : Type*)
  /-- The server `i` times out and starts an election. -/
  | timeout (i : S)
  /-- The server `i` becomes leader of the term `t`. -/
  | becomeLeader (i : S) (t : ℕ)
  /-- A client hands the command `c` to the leader `i`. -/
  | clientRequest (i : S) (c : C)
  /-- The leader `i` sends the server `j` an AppendEntries request with at most `k` entries. -/
  | appendEntries (i j : S) (k : ℕ)
  /-- The leader `i` sets its `commitIndex` to `n`. -/
  | advanceCommitIndex (i : S) (n : ℕ)
  /-- The server `i` applies the command `c` of its entry at index `n` to its state machine. -/
  | apply (i : S) (n : ℕ) (c : C)
  /-- The server `m.dst` receives the message `m`. -/
  | receive (m : Message S C)
  /-- The network loses a copy of the message `m`. -/
  | drop (m : Message S C)
  /-- The network duplicates the message `m`. -/
  | duplicate (m : Message S C)
  /-- The server `i` crashes. -/
  | crash (i : S)
  /-- The server `i` recovers. -/
  | recover (i : S)

variable [DecidableEq S]

namespace Server

/- **How a Raft server handles a message** (Ongaro and Ousterhout, Figure 2). The server first
applies the rule for a newer term to the message's term (`observeTerm`); then, for a message from
the server `j`:

* RequestVote with term `t`: the server grants its vote, setting `votedFor` to `j`, when `t` is its
  current term, it has voted for no one or for `j`, and the candidate's last entry makes its log
  at least as up to date as the server's (`AtLeastAsUpToDate`); it replies with its current term
  and whether it granted its vote.
* AppendEntries with term `t`, preceding index `p`, preceding term `q`, entries `es` and leader
  commit `c`: if `t` is below its current term, the server replies false. Otherwise a leader
  ignores the request, and a follower or candidate becomes a follower; it replies false if its log
  fails the consistency check for `p` and `q` (`PrevMatches`), and otherwise replaces its log `l`
  by the first `p` entries of `l` followed by `mergeEntries` of the others and `es`, sets
  `commitIndex` to the smaller of `c` and `p + |es|` if `c` exceeds `commitIndex`, and replies
  true with the match index `p + |es|`.
* A RequestVote response carrying the current term and granting the vote: a candidate adds `j`
  to `votesGranted`.
* An AppendEntries response carrying the current term: a leader, on success with match index
  `k`, sets `nextIndex j` to `k + 1` and `matchIndex j` to the larger of `matchIndex j` and `k`,
  and on failure lowers `nextIndex j` by one, but not below `1`.

The server ignores any other response. The result is the server's new state and its reply, at
most one message, to `j`. -/
def handle (sv : Server S C) (m : Message S C) : Server S C × Multiset (Message S C) :=
  let sv := sv.observeTerm m.payload.term
  match m.payload with
  | .requestVote t n lt =>
    if t = sv.currentTerm ∧ (sv.votedFor = none ∨ sv.votedFor = some m.src) ∧
        AtLeastAsUpToDate lt n sv.log then
      ({ sv with votedFor := some m.src },
        {⟨m.dst, m.src, .requestVoteReply sv.currentTerm true⟩})
    else (sv, {⟨m.dst, m.src, .requestVoteReply sv.currentTerm false⟩})
  | .appendEntries t p q es c =>
    if t < sv.currentTerm then
      (sv, {⟨m.dst, m.src, .appendEntriesReply sv.currentTerm false 0⟩})
    else if sv.role = .leader then (sv, 0)
    else if PrevMatches sv.log p q then
      ({ sv with
          role := .follower
          log := sv.log.take p ++ mergeEntries (sv.log.drop p) es
          commitIndex := if sv.commitIndex < c then min c (p + es.length) else sv.commitIndex },
        {⟨m.dst, m.src, .appendEntriesReply sv.currentTerm true (p + es.length)⟩})
    else
      ({ sv with role := .follower },
        {⟨m.dst, m.src, .appendEntriesReply sv.currentTerm false 0⟩})
  | .requestVoteReply t g =>
    if sv.role = .candidate ∧ t = sv.currentTerm ∧ g = true then
      ({ sv with votesGranted := insert m.src sv.votesGranted }, 0)
    else (sv, 0)
  | .appendEntriesReply t ok k =>
    if sv.role = .leader ∧ t = sv.currentTerm then
      if ok then
        ({ sv with
            nextIndex := Function.update sv.nextIndex m.src (k + 1)
            matchIndex := Function.update sv.matchIndex m.src (max (sv.matchIndex m.src) k) }, 0)
      else
        ({ sv with
            nextIndex := Function.update sv.nextIndex m.src (max (sv.nextIndex m.src - 1) 1) }, 0)
    else (sv, 0)

omit [DecidableEq S] in
theorem currentTerm_observeTerm (sv : Server S C) (t : ℕ) :
    (sv.observeTerm t).currentTerm = max sv.currentTerm t := by
  unfold observeTerm
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (not_lt.mp h)).symm

theorem currentTerm_handle (sv : Server S C) (m : Message S C) :
    (sv.handle m).1.currentTerm = max sv.currentTerm m.payload.term := by
  obtain ⟨src, dst, p⟩ := m
  rw [← currentTerm_observeTerm]
  cases p <;> simp only [handle] <;> split_ifs <;> rfl

theorem votedFor_handle {sv : Server S C} {m : Message S C} {j : S}
    (ht : (sv.handle m).1.currentTerm = sv.currentTerm) (hv : sv.votedFor = some j) :
    (sv.handle m).1.votedFor = some j := by
  have hle : m.payload.term ≤ sv.currentTerm := by
    rw [currentTerm_handle] at ht; omega
  have hobs : sv.observeTerm m.payload.term = sv := by
    simp [observeTerm, not_lt.mpr hle]
  obtain ⟨src, dst, p⟩ := m
  simp only at hobs
  cases p <;> simp only [handle, hobs] <;> split_ifs with hc <;> try exact hv
  obtain ⟨-, hnone | hsrc, -⟩ := hc
  · simp [hv] at hnone
  · simpa [hv] using hsrc.symm

end Server

variable [Fintype S]

/- **One step of the Raft protocol** (Ongaro and Ousterhout, Figure 2). Each event of a server
`i` other than its recovery requires `i` to be up.

* `timeout i`: a follower or candidate increments its `currentTerm`, becomes a candidate, votes
  for itself (`votedFor := i`, `votesGranted := {i}`) and sends every other server a RequestVote
  request with its new term and the index and term of its last log entry.
* `becomeLeader i t`: a candidate whose `votesGranted` is a majority of the servers, `t` being its
  current term, becomes leader and sets every `nextIndex` to its last log index plus one and
  every `matchIndex` to `0`.
* `clientRequest i c`: a leader appends the entry of term `currentTerm` and command `c` to its log.
* `appendEntries i j k`: a leader sends a server `j ≠ i` an AppendEntries request with its current
  term, the preceding index `p = nextIndex j - 1`, the preceding term `termAt log p`, the first
  `k` entries of its log after index `p` (all of them if there are fewer; none for a heartbeat)
  and its `commitIndex`.
* `advanceCommitIndex i n`: a leader sets `commitIndex` to `n` when `n` exceeds it, its log has an
  entry at index `n` whose term is `currentTerm`, and a majority of the servers `j` have
  `matchIndex j ≥ n`, the leader counting itself with its last log index in place of a
  `matchIndex`.
* `apply i n c`: a server with `lastApplied < commitIndex` whose log has, at the index
  `n = lastApplied + 1`, an entry with command `c` sets `lastApplied` to `n`.
* `receive m`: the receiver `m.dst` takes one copy of `m` out of the network and handles it
  (`Server.handle`); its reply, if any, enters the network.
* `drop m`, `duplicate m`: the network loses one copy of a message in flight, or adds one.
* `crash i`: the server crashes (`Server.crash`); `recover i`: a crashed server comes back up. -/
inductive Step : State S C → Event S C → State S C → Prop
  | timeout (s : State S C) (i : S) :
      (s.server i).up → (s.server i).role ≠ .leader →
      Step s (.timeout i)
        ⟨Function.update s.server i { s.server i with
            currentTerm := (s.server i).currentTerm + 1
            role := .candidate
            votedFor := some i
            votesGranted := {i} },
          s.network + (Finset.univ.erase i).val.map fun j =>
            ⟨i, j, .requestVote ((s.server i).currentTerm + 1) (s.server i).log.length
              (termAt (s.server i).log (s.server i).log.length)⟩⟩
  | becomeLeader (s : State S C) (i : S) :
      (s.server i).up → (s.server i).role = .candidate →
      Fintype.card S < 2 * (s.server i).votesGranted.card →
      Step s (.becomeLeader i (s.server i).currentTerm)
        { s with server := Function.update s.server i { s.server i with
            role := .leader
            nextIndex := fun _ => (s.server i).log.length + 1
            matchIndex := fun _ => 0 } }
  | clientRequest (s : State S C) (i : S) (c : C) :
      (s.server i).up → (s.server i).role = .leader →
      Step s (.clientRequest i c)
        { s with server := Function.update s.server i { s.server i with
            log := (s.server i).log ++ [⟨(s.server i).currentTerm, c⟩] } }
  | appendEntries (s : State S C) (i j : S) (k : ℕ) :
      (s.server i).up → (s.server i).role = .leader → j ≠ i →
      Step s (.appendEntries i j k)
        { s with network :=
            ⟨i, j, .appendEntries (s.server i).currentTerm ((s.server i).nextIndex j - 1)
              (termAt (s.server i).log ((s.server i).nextIndex j - 1))
              (((s.server i).log.drop ((s.server i).nextIndex j - 1)).take k)
              (s.server i).commitIndex⟩ ::ₘ s.network }
  | advanceCommitIndex (s : State S C) (i : S) (n : ℕ) :
      (s.server i).up → (s.server i).role = .leader → (s.server i).commitIndex < n →
      n ≤ (s.server i).log.length → termAt (s.server i).log n = (s.server i).currentTerm →
      Fintype.card S < 2 * (Finset.univ.filter fun j =>
        n ≤ if j = i then (s.server i).log.length else (s.server i).matchIndex j).card →
      Step s (.advanceCommitIndex i n)
        { s with server := Function.update s.server i { s.server i with commitIndex := n } }
  | apply (s : State S C) (i : S) (e : Entry C) :
      (s.server i).up → (s.server i).lastApplied < (s.server i).commitIndex →
      (s.server i).log[(s.server i).lastApplied]? = some e →
      Step s (.apply i ((s.server i).lastApplied + 1) e.cmd)
        { s with server := Function.update s.server i { s.server i with
            lastApplied := (s.server i).lastApplied + 1 } }
  | receive (s : State S C) (m : Message S C) (rest : Multiset (Message S C)) :
      s.network = m ::ₘ rest → (s.server m.dst).up →
      Step s (.receive m)
        ⟨Function.update s.server m.dst ((s.server m.dst).handle m).1,
          rest + ((s.server m.dst).handle m).2⟩
  | drop (s : State S C) (m : Message S C) (rest : Multiset (Message S C)) :
      s.network = m ::ₘ rest → Step s (.drop m) { s with network := rest }
  | duplicate (s : State S C) (m : Message S C) :
      m ∈ s.network → Step s (.duplicate m) { s with network := m ::ₘ s.network }
  | crash (s : State S C) (i : S) :
      (s.server i).up →
      Step s (.crash i) { s with server := Function.update s.server i (s.server i).crash }
  | recover (s : State S C) (i : S) :
      (s.server i).up = false →
      Step s (.recover i)
        { s with server := Function.update s.server i { s.server i with up := true } }

/-- **The Raft consensus protocol** (Ongaro and Ousterhout, Figure 2, without cluster membership
changes or log compaction), as a CSLib labelled transition system. Its states are the states of
the servers together with the multiset of messages in flight, its labels are the events (`Event`)
and its transitions the steps (`Step`): election timeouts at any moment, elections, client
requests, replication, commitment and application, the receipt of a message (`Server.handle`),
the loss or duplication of a message by the network, and the crash and recovery of a server.
We model initialized Raft runs by taking traces of `lts` from `State.init`; `lts` itself also
admits traces from other states. -/
def lts : Cslib.LTS (State S C) (Event S C) := ⟨Step⟩

/-! ### Terms never decrease -/

theorem currentTerm_le_of_step {s s' : State S C} {μ : Event S C} (h : Step s μ s') (i : S) :
    (s.server i).currentTerm ≤ (s'.server i).currentTerm := by
  cases h with
  | receive m rest _ _ =>
    simp only [Function.update_apply]
    split_ifs with hi
    · subst hi; rw [Server.currentTerm_handle]; exact le_max_left _ _
    · exact le_rfl
  | appendEntries | drop | duplicate => exact le_rfl
  | _ =>
    simp only [Function.update_apply]
    split_ifs with hi
    · subst hi; simp [Server.crash]
    · exact le_rfl

/-- **Terms never decrease in Raft.** For every sequence of steps from any state, the
`currentTerm` of every server stays the same or increases, crashes and recoveries included. -/
theorem currentTerm_le_of_mTr {s s' : State S C} {μs : List (Event S C)}
    (h : lts.MTr s μs s') (i : S) : (s.server i).currentTerm ≤ (s'.server i).currentTerm := by
  induction h with
  | refl => exact le_rfl
  | stepL hstep _ ih => exact (currentTerm_le_of_step hstep i).trans ih

/-! ### Votes are never changed within a term -/

theorem votedFor_eq_of_step {s s' : State S C} {μ : Event S C} (h : Step s μ s') {i j : S}
    (ht : (s'.server i).currentTerm = (s.server i).currentTerm)
    (hv : (s.server i).votedFor = some j) : (s'.server i).votedFor = some j := by
  cases h with
  | receive m rest _ _ =>
    simp only [Function.update_apply] at ht ⊢
    split_ifs at ht ⊢ with hi
    · subst hi; exact Server.votedFor_handle ht hv
    · exact hv
  | timeout =>
    simp only [Function.update_apply] at ht ⊢
    split_ifs at ht ⊢ with hi
    · subst hi; simp at ht
    · exact hv
  | appendEntries | drop | duplicate => exact hv
  | _ =>
    simp only [Function.update_apply]
    split_ifs with hi
    · subst hi; simpa [Server.crash] using hv
    · exact hv

/- **A Raft server's vote is never changed within a term.** For every sequence of steps from any
state after which the `currentTerm` of a server is what it was, a vote the server had cast for `j`
at the start is still its vote at the end, crashes and recoveries included. -/
theorem votedFor_eq_of_mTr {s s' : State S C} {μs : List (Event S C)} (h : lts.MTr s μs s')
    {i j : S} (ht : (s'.server i).currentTerm = (s.server i).currentTerm)
    (hv : (s.server i).votedFor = some j) : (s'.server i).votedFor = some j := by
  induction h with
  | refl => exact hv
  | @stepL s₁ μ s₂ μs s₃ hstep hrest ih =>
    have h₁ := currentTerm_le_of_step hstep i
    have h₂ := currentTerm_le_of_mTr hrest i
    have heq : (s₂.server i).currentTerm = (s₁.server i).currentTerm := by omega
    exact ih (by omega) (votedFor_eq_of_step hstep heq hv)

/-! ### A single-server cluster commits a command -/

/-- **A single-server Raft cluster elects itself and commits a command.** In a cluster with a
single server `i`, for every command `c` there is an execution from the initial state in which
`i` times out, becomes leader of term `1`, receives the client command `c`, sets its
`commitIndex` to `1` and applies `c` at index `1`. At its end `i` is the leader, its log is the
single entry of term `1` and command `c`, and its `commitIndex` and `lastApplied` are `1`. -/
theorem exists_mTr_commit_of_subsingleton [Subsingleton S] (i : S) (c : C) :
    ∃ s : State S C, lts.MTr State.init
        [.timeout i, .becomeLeader i 1, .clientRequest i c, .advanceCommitIndex i 1,
          .apply i 1 c] s ∧
      (s.server i).role = .leader ∧ (s.server i).log = [⟨1, c⟩] ∧
      (s.server i).commitIndex = 1 ∧ (s.server i).lastApplied = 1 := by
  have hupd : ∀ (f : S → Server S C) (v : Server S C), Function.update f i v = fun _ => v := by
    intro f v; funext j; rw [Subsingleton.elim j i, Function.update_self]
  have herase : Finset.univ.erase i = ∅ := by
    ext j; simp [Subsingleton.elim j i]
  have hcard : Fintype.card S = 1 := Fintype.card_eq_one_iff.mpr ⟨i, fun j => Subsingleton.elim j i⟩
  let sv₁ : Server S C :=
    { (Server.init : Server S C) with
      currentTerm := 1, role := .candidate, votedFor := some i, votesGranted := {i} }
  let sv₂ : Server S C := { sv₁ with role := .leader, nextIndex := (fun _ => 1) }
  let sv₃ : Server S C := { sv₂ with log := [⟨1, c⟩] }
  let sv₄ : Server S C := { sv₃ with commitIndex := 1 }
  let sv₅ : Server S C := { sv₄ with lastApplied := 1 }
  refine ⟨⟨fun _ => sv₅, 0⟩, ?_, rfl, rfl, rfl, rfl⟩
  have h₁ : Step (State.init : State S C) (.timeout i) ⟨fun _ => sv₁, 0⟩ := by
    have := Step.timeout (State.init : State S C) i rfl (by simp [State.init, Server.init])
    rw [herase] at this
    simpa [hupd, State.init, Server.init, sv₁] using this
  have h₂ : Step (⟨fun _ => sv₁, 0⟩ : State S C) (.becomeLeader i 1) ⟨fun _ => sv₂, 0⟩ := by
    have := Step.becomeLeader (⟨fun _ => sv₁, 0⟩ : State S C) i rfl rfl
      (by rw [hcard]; simp [sv₁])
    simpa [hupd, sv₁, sv₂, Server.init] using this
  have h₃ : Step (⟨fun _ => sv₂, 0⟩ : State S C) (.clientRequest i c) ⟨fun _ => sv₃, 0⟩ := by
    have := Step.clientRequest (⟨fun _ => sv₂, 0⟩ : State S C) i c rfl rfl
    simpa [hupd, sv₁, sv₂, sv₃, Server.init] using this
  have h₄ : Step (⟨fun _ => sv₃, 0⟩ : State S C) (.advanceCommitIndex i 1)
      ⟨fun _ => sv₄, 0⟩ := by
    have hall : (Finset.univ.filter fun j : S => 1 ≤ if j = i then sv₃.log.length
        else sv₃.matchIndex j) = Finset.univ := by
      ext j; simp [Subsingleton.elim j i, sv₃]
    have := Step.advanceCommitIndex (⟨fun _ => sv₃, 0⟩ : State S C) i 1 rfl rfl
      (by simp [sv₃, sv₂, sv₁, Server.init]) (by simp [sv₃]) rfl
      (by simp only [hall, Finset.card_univ, hcard]; omega)
    simpa [hupd, sv₄] using this
  have h₅ : Step (⟨fun _ => sv₄, 0⟩ : State S C) (.apply i 1 c) ⟨fun _ => sv₅, 0⟩ := by
    have := Step.apply (⟨fun _ => sv₄, 0⟩ : State S C) i ⟨1, c⟩ rfl
      (by simp [sv₄, sv₃, sv₂, sv₁, Server.init]) (by simp [sv₄, sv₃, sv₂, sv₁, Server.init])
    simpa [hupd, sv₄, sv₅, sv₃, sv₂, sv₁, Server.init] using this
  exact .stepL h₁ (.stepL h₂ (.stepL h₃ (.stepL h₄ (.stepL h₅ .refl))))

end Cslib.Distributed.Raft
