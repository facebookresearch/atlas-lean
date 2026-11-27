# Synchronization is undecidable for wait-only non-blocking rendez-vous protocols

For networks of any number of identical processes communicating by rendez-vous with non-blocking requests, it is undecidable whether some initial number of processes can reach a configuration with every process in the final state. This holds already for wait-only protocols, where each state either only sends and acts internally or only receives.

**Theorem.** The synchronization problem is undecidable for [rendez-vous protocols with non-blocking semantics](rendez-vous-protocols-non-blocking.md): there is no algorithm that, given a rendez-vous protocol $\mathcal{P} = (Q, \Sigma, q_{in}, q_f, T)$, decides whether there are an initial configuration $C_0$ and a configuration $C_f$ with all processes in $q_f$ such that $C_0 \to^* C_f$ under the non-blocking semantics. The problem stays undecidable when the input is restricted to wait-only protocols.

## Depends on

- [Rendez-vous protocols with non-blocking semantics](rendez-vous-protocols-non-blocking.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces from the following problem for two-counter (Minsky) machines: given a machine $M$ with initial location $\ell_0$ and a location $\ell_f$, is there an execution from $(\ell_0, 0, 0)$ to $(\ell_f, 0, 0)$? One may assume $\ell_f$ has no outgoing transitions. The protocol built in the source contains a copy of the control of $M$, entered by one process after an initialization handshake, and, for each counter $i$, unit states $0_i$ and $1_i$: a process in $0_i$ answers an increment of counter $i$ and moves to $1_i$, and a process in $1_i$ answers a decrement and moves to the final state. A zero test of counter $i$ is a non-blocking request that any process in $1_i$ would answer by moving to a sink state from which the final state is unreachable, so a reachable configuration with all processes in the final state cannot contain an incorrect zero test, and every unit used for an increment must have been decremented again. The source shows that such a configuration is reachable from some initial configuration exactly when $M$ has an execution from $(\ell_0, 0, 0)$ to $(\ell_f, 0, 0)$; the protocol is wait-only.

A good expansion links the undecidability of reaching a given location with both counters equal to $0$ for two-counter machines, which follows from the universality of two-counter machines by emptying the counters before halting.

In contrast, the source shows that coverability of a configuration under the same semantics is complete for exponential space, and solvable in polynomial time for wait-only protocols.

## Sources

- Lucie Guillou, Arnaud Sangnier and Nathalie Sznajder, "Safety Analysis of Parameterised Networks with Non-Blocking Rendez-Vous", in *34th International Conference on Concurrency Theory (CONCUR 2023)*, Leibniz International Proceedings in Informatics 279, article 7, pp. 7:1–7:17, 2023, doi:[10.4230/LIPIcs.CONCUR.2023.7](https://doi.org/10.4230/LIPIcs.CONCUR.2023.7); read in arXiv:2307.04546v1 ([arXiv](https://arxiv.org/abs/2307.04546v1)): Theorem 6.1 (Section 6) of that version, with the reduction and its figures in the appendix.
