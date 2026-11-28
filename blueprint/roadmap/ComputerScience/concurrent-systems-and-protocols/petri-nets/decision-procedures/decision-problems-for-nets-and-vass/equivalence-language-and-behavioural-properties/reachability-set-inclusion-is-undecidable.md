# Inclusion of reachability sets of Petri nets is undecidable

It is undecidable whether every marking reachable in one Petri net is also reachable in another net with the same places; Rabin's proof reduces Hilbert's tenth problem.

**Marking inclusion.** Given two ordinary [Petri nets](../../../place-transition-petri-nets.md) $(N_1, M_{01})$ and $(N_2, M_{02})$ (all arcs of weight $1$, as in the survey's Section 2) with the same set of places, the *marking inclusion problem* asks whether the [reachability set](../../../reachability-set-and-reachability-graph.md) of the first is contained in that of the second.

**Theorem (Rabin).** The marking inclusion problem for ordinary Petri nets is undecidable.

Petri nets and vector addition systems are interreducible, so the analogous problem for vector addition systems is undecidable too; no cited source states that form, so it is a remark here.

Rabin did not publish the result; Baker described the proof in a technical memo, and Hack used it to prove that equality of reachability sets is undecidable.

## Depends on

- [Reachability set and reachability graph](../../../reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Vector addition systems](../../../vector-addition-systems.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

As the survey describes it, the proof relies on a subtle way of computing functions by nets in a weak sense: Diophantine polynomials can be computed in this sense, and Hilbert's tenth problem, undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, is then reduced to the marking inclusion problem. A good expansion links a page for the weak computation of Diophantine polynomials by nets, with a source that gives its proof.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 4, paragraph "Marking equivalence", of arXiv:2411.01592v1, which states the result and its proof idea and credits it to Rabin and to Baker's memo.
