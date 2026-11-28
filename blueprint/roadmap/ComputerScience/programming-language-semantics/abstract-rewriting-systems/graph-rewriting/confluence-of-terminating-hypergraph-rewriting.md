# Confluence of finite terminating hypergraph rewriting systems is undecidable

There is no algorithm that decides, given a finite hypergraph rewriting system that is terminating, whether it is confluent. Terminating term rewriting systems, in contrast, have decidable confluence by the critical pair lemma.

**Theorem.** The following problem is undecidable. Input: a finite hypergraph rewriting system $\mathcal{G} = \langle \mathcal{C}, \mathcal{R} \rangle$ in the sense of [hypergraph rewriting systems](hypergraph-rewriting-systems.md) that is terminating (finite node and edge label sets and a finite set of rules, all part of the input). Question: is $\mathcal{G}$ confluent? The undecidability holds already on inputs promised to be terminating: no algorithm answers correctly on every finite terminating system.

## Depends on

- [Hypergraph rewriting systems](hypergraph-rewriting-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof follows the Kapur–Narendran–Otto argument that ground confluence of terminating term rewriting is undecidable. From a Post instance $A = \langle u_1, \dots, u_n \rangle$, $B = \langle v_1, \dots, v_n \rangle$ of nonempty words one builds a finite terminating system $\mathcal{G}(A, B)$ with a single node label. One group of rules creates a critical pair standing for the choice between extending an index sequence and checking it; a second group tests whether an index sequence encoded as a hyperedge path is a solution, a third detects ill-formed hypergraphs, and a fourth collects garbage. The two sides of the critical pair can always be joined unless some index sequence is a solution, so $\mathcal{G}(A, B)$ is confluent exactly when $\langle A, B \rangle$ has no solution.

For terminating term rewriting systems the problem is decidable: compute normal forms of all critical pairs (Knuth and Bendix). The hypergraph case fails because joinable critical pairs need not imply local confluence.

## Sources

- Detlef Plump, "Hypergraph rewriting: critical pairs and undecidability of confluence", chapter 15 of M. R. Sleep, M. J. Plasmeijer and M. C. J. D. van Eekelen (eds.), *Term Graph Rewriting: Theory and Practice*, John Wiley & Sons, 201–213, 1993, read as the [accepted version](https://eprints.whiterose.ac.uk/id/eprint/243833/): Theorem 15.4.1 and its proof in Section 15.4.
