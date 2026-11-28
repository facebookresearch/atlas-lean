# Fair non-termination of Petri nets is complete for the first level of the analytical hierarchy

Whether a Petri net has an infinite fair occurrence sequence, one in which every transition enabled at infinitely many markings occurs infinitely often, is complete for the first level of the analytical hierarchy, and hence undecidable.

**Fairness.** Nets are ordinary [Petri nets](../../../place-transition-petri-nets.md) (all arcs of weight $1$, as in the survey's Section 2). An infinite occurrence sequence of a net is *fair* if every transition that is enabled at infinitely many markings of the sequence occurs infinitely often in it. The *fair non-termination problem* asks, given an ordinary Petri net, whether it has an infinite fair occurrence sequence (that is, whether it is not guaranteed to terminate under the fairness assumption). For $i \in \mathbb{N}$, a transition is *$i$-enabled* at a marking if some occurrence sequence of length at most $i$ enables it, and an infinite sequence is *$i$-fair* if every transition that is $i$-enabled infinitely often along it occurs infinitely often; $0$-fairness is fairness.

**Theorem (Carstensen; Howell, Rosier and Yen).**

1. The fair non-termination problem is undecidable (Carstensen), and it is complete for the first level of the analytical hierarchy (Howell, Rosier and Yen).
2. For every $i$, the $i$-fair non-termination problem is undecidable (Howell, Rosier and Yen).

The restriction of fair non-termination to bounded nets is decidable but not primitive recursive. Impartial non-termination reduces to boundedness, just non-termination is decidable (Jančar), and $\infty$-fair non-termination reduces to reachability.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The problem asks for an infinite object, a fair occurrence sequence, and the cited completeness result shows that it is as hard as any problem of the first level of the analytical hierarchy, in particular undecidable. The survey gives no proof details; the comparisons with impartial, just and $\infty$-fair non-termination show that the difficulty comes from the particular fairness notion. A good expansion follows a source that proves the completeness result and links a page for the first level of the analytical hierarchy.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 3, paragraph "Non-termination", of arXiv:2411.01592v1, which defines fairness and $i$-fairness and states both clauses and the comparisons.
