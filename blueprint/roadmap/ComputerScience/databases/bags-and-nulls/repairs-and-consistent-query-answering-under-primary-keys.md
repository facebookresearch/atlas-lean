# Repairs and consistent query answering under primary keys

This node collects consistent query answering under primary keys and the attack-graph
classification for self-join-free Boolean conjunctive queries.

## Expansion

A sound expansion has separate pages for:

1. **Repairs.** For a schema with one primary key per relation, a block is a maximal set of facts of
   one relation that agree on its key; a repair is a subinstance that contains exactly one fact of every block.
2. **CERTAINTY.** For a Boolean query $q$, $\mathrm{CERTAINTY}(q)$ asks whether $q$ holds in every repair.
3. **Attack graph.** For a self-join-free Boolean conjunctive query, the full definitions from the
   source: the closure of an atom's key under the functional dependencies of the other atoms, the
   attack relation between atoms, and weak attacks.
4. **Classification.** The complexity of $\mathrm{CERTAINTY}(q)$ determined by the attack graph (acyclic,
   cycles of weak attacks only, or a strong cycle), each case with its exact complexity class from the
   source.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Depends on

- [Functional dependency](../functional-dependencies/fd.md)

## Sources

- A Trichotomy in the Data Complexity of Certain Query Answering for Conjunctive Queries (Koutris, Wijsen), arXiv:1501.07864v1 — full version of the PODS 2015 paper, Section 3 (blocks and repairs, p. 3; CERTAINTY(q), p. 4), Section 4 (the sets $F^{+,q}$, attacks with witnesses, weak and strong attacks and cycles, p. 5) and Theorem 2 (the trichotomy, p. 6). <https://arxiv.org/pdf/1501.07864v1>
- A Dichotomy on the Complexity of Consistent Query Answering for Atoms with Simple Keys (Koutris, Suciu), arXiv:1212.6636 — arXiv (ICDT 2014). <https://arxiv.org/pdf/1212.6636> Background reference.
