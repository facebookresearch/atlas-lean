# Equality of reachability sets of Petri nets is undecidable

It is undecidable whether two Petri nets with the same places have the same set of reachable markings, already for nets with five unbounded places.

**Marking equivalence.** Two [Petri nets](../../../place-transition-petri-nets.md) $(N_1, M_{01})$ and $(N_2, M_{02})$ with the same set of places are *marking equivalent* if they have the same [reachability set](../../../reachability-set-and-reachability-graph.md), that is, the same set of reachable markings. A place $s$ is *unbounded* if for every $k$ some reachable marking puts more than $k$ tokens on $s$.

**Theorem (Hack).** Marking equivalence is undecidable for Petri nets: no algorithm decides, given two Petri nets with the same set of places, whether their reachability sets are equal. By a later proof of Jančar, it is undecidable even for nets with five unbounded places.

For bounded nets the problem is decidable (the reachability sets are finite), though not primitive recursive, and it is decidable for classes of nets with effectively semilinear reachability sets.

## Depends on

- [Reachability set and reachability graph](../../../reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Inclusion of reachability sets of Petri nets is undecidable](reachability-set-inclusion-is-undecidable.md)

## Expansion

Hack's proof builds on Rabin's undecidability of reachability set inclusion: nets compute Diophantine polynomials in a weak sense, so Hilbert's tenth problem reduces to inclusion and then to equality of reachability sets. Jančar's proof instead semi-simulates a counter machine by a net that may wrongly take a zero-test branch while a counter is nonzero, and builds two variants of this net that are marking equivalent iff the machine does not halt.

## Sources

- Michel Hack, "The equality problem for vector addition systems is undecidable", *Theoretical Computer Science* 2(1):77–95, 1976, doi:10.1016/0304-3975(76)90008-6 (not read; the original refereed source).
- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 4, paragraph "Marking equivalence", of arXiv:2411.01592v1, which states both results (crediting the five-place bound to Jančar's STACS 1994 paper).
- Petr Jančar, "Decidability questions for bisimilarity of Petri nets and some related problems", in *STACS 94*, Lecture Notes in Computer Science 775, Springer, 1994, pp. 581–592, doi:10.1007/3-540-57785-8_173 (not read; the paper the survey cites), and its journal version "Undecidability of bisimilarity for Petri nets and some related problems", *Theoretical Computer Science* 148(2):281–301, 1995, doi:10.1016/0304-3975(95)00037-W (not read; the journal version of the paper the survey cites for the five-place bound).
