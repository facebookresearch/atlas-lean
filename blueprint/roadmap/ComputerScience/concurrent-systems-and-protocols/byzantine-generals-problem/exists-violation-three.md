# No protocol for three generals tolerates one traitor

Suppose there are at least two
possible orders. For every oral-message protocol for three generals $0$, $1$, $2$ with commander
$0$ and every number of rounds $T$, there are an order $v$, a general $t$ and a behaviour of $t$
such that, in the execution with order $v$ in which $t$ is the only traitor, the agreement
condition (IC1) or the validity condition (IC2) fails after $T$ rounds.

This is the theorem of Pease, Shostak and Lamport, proved by a commander version of the
hexagon argument of Fischer, Lynch and Merritt.

**Model.** Synchronous rounds; one Byzantine traitor, which may send different messages to different generals in every round; reliable links with known senders; no signatures; deterministic protocols. With unforgeable signatures the problem is solvable for three generals (Lamport, Shostak and Pease, §4, Theorem 2), so the absence of signatures is essential.

## Sources

- L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on Programming Languages and Systems 4(3), July 1982, 382–401: Section 2, pp. 384–385 (informal argument).
- M. Pease, R. Shostak, L. Lamport, *Reaching Agreement in the Presence of Faults*, Journal of the ACM 27(2), 1980, 228–234: the rigorous three-general impossibility proof, cited by Lamport, Shostak and Pease as their reference [3] (not consulted here).
