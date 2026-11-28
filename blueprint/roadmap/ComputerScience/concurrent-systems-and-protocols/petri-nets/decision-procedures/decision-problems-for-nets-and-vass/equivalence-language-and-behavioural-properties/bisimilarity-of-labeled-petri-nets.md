# Bisimilarity of labeled Petri nets is undecidable

Whether two labeled Petri nets are bisimilar, that is, whether their reachability graphs are related by a strong bisimulation from the initial markings, is undecidable, already for nets with only two unbounded places.

**Bisimilarity.** For labeled ordinary [Petri nets](../../../place-transition-petri-nets.md) (all arcs of weight $1$, as in the survey's Section 2), the reachability graph has the reachable markings as nodes and an edge $M \xrightarrow{a} M'$ when some transition with label $a$ leads from $M$ to $M'$. A relation $R$ between the nodes of two such graphs, taken on the disjoint union of their node sets so that it can be required to be symmetric, is a *(strong) bisimulation* if it is symmetric and whenever $(n_1, n_2) \in R$ and $n_1 \xrightarrow{a} n_1'$, there is $n_2'$ with $n_2 \xrightarrow{a} n_2'$ and $(n_1', n_2') \in R$. Two labeled nets are *bisimilar* if some bisimulation contains the pair of their initial markings.

**Theorem (Jančar).** Bisimilarity of labeled ordinary Petri nets is undecidable, even for nets with only two unbounded places.

Bisimilarity is decidable for labeled BPP-nets, for labeled nets when one of the two is deterministic up to bisimilarity, and for unlabeled nets, where bisimilarity coincides with trace equivalence; an unlabeled net is one whose labeling is injective (survey, Section 2), so bisimilarity of unlabeled nets compares transition identities.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../../../reachability-set-and-reachability-graph.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof follows the pattern Jančar introduced for equivalences of nets: a net semi-simulates a counter machine, with one place per counter, but may follow a zero-test branch while the counter is nonzero. Two modifications of this net are constructed such that the machine halts iff the two nets are not bisimilar. A good expansion links a page for Jančar's semi-simulation of counter machines by nets, from which both modified nets are built.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 4, paragraph "Bisimulation equivalence", of arXiv:2411.01592v1, which defines bisimilarity of nets as above and states the result and the decidable cases.
