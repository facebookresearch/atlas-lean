# A bivalent configuration survives any pending event

Let the set of processes be finite with at least two processes, and let $a$ be an algorithm that satisfies agreement (no state reachable from an input assignment has decided two different values) and from every reachable state can reach a decision without the participation of any one process (as in [A bivalent initial state](exists-bivalent-start.md)). If a state $s$ reachable from some input assignment is bivalent and the message $m$ is in flight in $s$, then some state $t$ reachable from $s$ without receiving $m$ still has $m$ in flight, and receiving $m$ in $t$ leads to a bivalent state. This is Lemma 3 of Fischer, Lynch and Paterson (1985), in the model of these pages: the event $e$ of receiving $m$ can be postponed until it no longer decides the outcome.

**Proof.** As in the source. Suppose every state of $\mathcal{D} = e(\mathcal{C})$ is univalent. Both values occur in $\mathcal{D}$, so along a schedule in $\mathcal{C}$ there are neighbours $g_1 \to g_2$, by a step $e'$, with $e(g_1)$ and $e(g_2)$ of different valences. If $e'$ is received by a process other than the receiver $p$ of $m$, then $e$ and $e'$ commute and $e(g_2)$ is reachable from $e(g_1)$, which is impossible. If both are received by $p$, take a decided state $A$ reachable from $g_1$ without $p$ (pseudo-termination); by commutativity $A$ reaches states below $e(g_1)$ and below $e(g_2)$, so $A$ would be bivalent although it has decided.

**Hypotheses.** As for [A bivalent initial state](exists-bivalent-start.md), the lemma is stated under what its proof uses rather than under the consensus condition for one fault, under which it would be vacuous. With exactly two processes it is vacuous all the same: no algorithm on two processes that satisfies agreement and reaches a decision without any one process has a reachable bivalent state. Each process alone can then reach a decision from every reachable state; by commutativity and agreement all these solo decisions from a state agree, and no step changes that common value, which is the decision of any decided state. For three or more processes the hypotheses can hold: informally, a Paxos-type algorithm in which any majority of the processes, in particular all but one, can complete a ballot satisfies them and has bivalent reachable states. The argument for two processes is not taken from the cited source.

## Informally uses

- [Commutativity of disjoint schedules](m-tr-comm.md): Lemma 1, used in both cases of the source's proof.

## Background

- [Bivalent state](bivalent.md): the conclusion.
- [Reachability without an event](reach-without.md): the set $\mathcal{C}$.

## Sources

- M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one faulty process*, Journal of the ACM 32(2), 1985, 374–382: Lemma 3.
