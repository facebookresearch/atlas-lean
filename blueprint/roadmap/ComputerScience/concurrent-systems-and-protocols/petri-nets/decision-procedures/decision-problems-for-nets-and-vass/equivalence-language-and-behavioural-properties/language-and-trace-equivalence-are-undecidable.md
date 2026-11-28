# Language and trace equivalence of labeled Petri nets are undecidable

Whether two labeled Petri nets have the same trace set, or the same language with respect to final markings, is undecidable, already for small numbers of unbounded places, while both problems are decidable for unlabeled nets.

**Labeled nets, traces and languages.** A *labeled* Petri net is a [Petri net](../../../place-transition-petri-nets.md) $(N, M_0)$ with a labeling $\ell$ that assigns a letter of an alphabet to each transition, not necessarily injectively; an unlabeled net is one with injective labeling. Its *trace set* is $T(N, M_0) = \{\ell(\sigma) : M_0 \xrightarrow{\sigma} M$ for some marking $M\}$, and its *language* with respect to a final marking $M^f$ is $L(N, M_0, M^f) = \{\ell(\sigma) : M_0 \xrightarrow{\sigma} M^f\}$, where $\sigma$ ranges over finite occurrence sequences. Two labeled nets are *trace equivalent* if they have the same trace set and *language equivalent* if they have the same language.

**Theorem.**

1. Trace equivalence and language equivalence of labeled Petri nets are undecidable (Hack).
2. Trace equivalence is undecidable already for labeled Petri nets with at most two unbounded places (Jančar).
3. Language equivalence is undecidable already when one of the two labeled nets has one unbounded place and the other has none (Valk and Vidal-Naquet).

For unlabeled nets both problems are decidable, by Hack's reduction to reachability. The survey reports that trace equivalence for labeled nets with exactly one unbounded place was open at the time of writing.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Reachability set and reachability graph](../../../reachability-set-and-reachability-graph.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Equality of reachability sets of Petri nets is undecidable](marking-equivalence-is-undecidable.md)

## Expansion

Hack reduces marking equivalence to trace and language equivalence. Araki and Kasami gave another proof by reduction from the halting problem for counter machines. Jančar's bound for trace equivalence comes from semi-simulating a counter machine with two counter places by two nets that agree on all traces iff the machine does not halt.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 2 (labeled nets, trace sets and languages) and Section 4, paragraph "Trace and language equivalences", of arXiv:2411.01592v1, which states all three clauses with their attributions.
- Michel Henri Théodore Hack, *Decidability questions for Petri nets*, PhD thesis, Massachusetts Institute of Technology, 1976 (not read; cited as the original source).
- Petr Jančar, "Decidability questions for bisimilarity of Petri nets and some related problems", in *STACS 94*, Lecture Notes in Computer Science 775, Springer, 1994, pp. 581–592, doi:10.1007/3-540-57785-8_173 (not read; the source of clause 2).
- Rüdiger Valk and Guy Vidal-Naquet, "Petri nets and regular languages", *Journal of Computer and System Sciences* 23(3):299–325, 1981, doi:10.1016/0022-0000(81)90067-2 (not read; the source of clause 3).
