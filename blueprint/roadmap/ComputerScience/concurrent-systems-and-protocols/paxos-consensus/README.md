# Paxos consensus

Lamport's single-decree Paxos ("the synod algorithm"), the consensus core of his state-machine approach to fault tolerance. Proposers issue numbered proposals, acceptors accept them, and a value is chosen once a quorum has accepted one proposal with that value. The safety requirements hold: at most one value is chosen, and only a proposed value is chosen. Termination is not guaranteed: by the [FLP theorem](../flp-impossibility/README.md) no deterministic asynchronous protocol can guarantee it in the presence of a crash.

**Model** (*Paxos Made Simple*, Section 2.1, "the customary asynchronous, non-Byzantine model"):

- *Synchrony:* none. Actions of all agents interleave in any order; there are no clocks and no timeouts.
- *Failures:* agents may stop and restart; acceptors keep their promises and acceptances across restarts (stable storage); proposers may forget everything. No Byzantine behaviour.
- *Messages:* sent messages persist in sets and may be used any number of times or never, so they may be delayed without bound, duplicated, reordered or lost; they are never corrupted.

**Structure.** The argument comes in two layers, as in Section 2.2 of the paper.

1. *Voting.* Over any history of proposals and acceptances in which proposal numbers are unique, only issued proposals are accepted, and Lamport's condition P2c holds, his induction on proposal numbers proves P2b, hence that all chosen proposals share one value. Quorums are any family of pairwise intersecting acceptor sets; majorities are the instance Lamport uses.
2. *Algorithm.* Phases 1 and 2 (prepare, promise, propose, accept) form a labelled transition system. An inductive invariant (acceptors' reports stay truthful because of their promises; every proposal is justified by a quorum of reports) shows that every reachable state is a voting history, so the safety theorems apply.

**Scope.** An acceptor's response to the prepare request $n$ reports its highest-numbered acceptance with number less than $n$, as in step 1(b) of the derivation in Section 2.2 (p. 4). The summary of Phase 1(b) on p. 5 states the response without that bound ("the highest-numbered proposal (if any) that it has accepted"); the two differ when an acceptor has accepted a proposal numbered above $n$ without having answered a prepare request numbered $n$ or more, which rule P1a allows. The theorems below are about the algorithm of Section 2.2 with the response of step 1(b), not about that variant. Within it, the model allows some extra behaviour (an acceptor need not ignore a prepare request for a proposal it already accepted, and any quorum system may replace majorities). Learners (Section 2.3) and the third safety requirement, that a process learns only chosen values, are outside the model.

## Voting

- [Quorum system](quorum-system.md)
- [Majorities form a quorum system](majority.md)
- [A Paxos voting history](voting.md)
- [Chosen proposal](chosen-at.md)
- [Chosen value](chosen.md)
- [Lamport's P2b](p2b.md)
- [At most one value is chosen](chosen-unique.md)
- [Only a proposed value is chosen](proposed-of-chosen.md)

## The algorithm

- [State of the single-decree Paxos algorithm](state.md)
- [Initial state of single-decree Paxos](init.md)
- [Actions of single-decree Paxos](action.md)
- [Highest-numbered acceptance below a number](highest-below.md)
- [Lamport's value rule](safe-value.md)
- [One step of single-decree Paxos](step.md)
- [Single-decree Paxos as a labelled transition system](lts.md)
- [Chosen value in a state](value-chosen.md)
- [The inductive invariant of single-decree Paxos](inv.md)
- [The Paxos invariant holds initially](inv-init.md)
- [Every step of single-decree Paxos preserves the invariant](inv-step.md)
- [The Paxos invariant holds in every reachable state](inv-of-can-reach.md)
- [Reachable states are Paxos voting histories](voting-of-inv.md)
- [Paxos safety: at most one value is chosen](chosen-unique-of-can-reach.md)
- [Paxos safety: only a proposed value is chosen](proposed-of-chosen-of-can-reach.md)

## Related topics

- [FLP impossibility](../flp-impossibility/README.md): in the same asynchronous crash-failure setting no deterministic protocol guarantees termination, which is why Paxos guarantees safety unconditionally and progress only under extra assumptions (Section 2.4).
- [Synchronous consensus with crash failures](../synchronous-consensus-with-crash-failures/README.md): with synchrony, consensus terminates despite crashes, at a cost of $f + 1$ rounds.
- [Byzantine generals problem](../byzantine-generals-problem/README.md): agreement when faulty processes may lie, which Paxos's non-Byzantine model excludes.
- [Labelled transition systems](../../process-calculi/labelled-transition-systems/README.md): the semantic model of the algorithm.
- [Input/output automata](../../process-calculi/input-output-automata/README.md): Lynch and Tuttle's model of asynchronous distributed systems, an alternative way to present such algorithms.
- [Lamport clocks](../lamport-clocks/README.md): the total ordering of events that the state-machine approach needs; Paxos, run once per command (Section 3), provides one despite failures.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.1 (problem and model), Section 2.2 (P1, P2, P2a, P2b, P2c, P1a, Phases 1 and 2).
