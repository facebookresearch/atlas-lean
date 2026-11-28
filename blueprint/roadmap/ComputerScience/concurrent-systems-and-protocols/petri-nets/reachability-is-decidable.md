# Reachability in Petri nets is decidable

There is an algorithm that decides, given a [Petri net](place-transition-petri-nets.md) $(N, M_0)$ and a marking $M$, whether $M$ is in the [reachability set](reachability-set-and-reachability-graph.md) $R(N, M_0)$. Mayr gave the first complete proof, Kosaraju a simpler one; all known algorithms of that period require non-primitive-recursive space. Leroux's algorithm runs two searches in parallel, one for a firing sequence from $M_0$ to $M$ and one for a Presburger-definable inductive invariant that contains $M_0$ but not $M$.

## Depends on

- [Reachability set and reachability graph](reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Non-reachability in Petri nets has a semilinear inductive invariant](decision-procedures/non-reachability-has-a-semilinear-inductive-invariant.md)
- [Semilinear sets are the sets definable in Presburger arithmetic](decision-procedures/semilinear-sets-are-the-presburger-definable-sets.md)
- [Quantifier elimination for Presburger arithmetic](../../../Logic/first-order-logic/quantifier-elimination-for-presburger-arithmetic/quantifier-elimination-for-presburger-arithmetic.md)

## Expansion

This page becomes ready once:

- A page reducing reachability in Petri nets with arc weights to reachability in ordinary Petri nets, or to vector addition systems in Leroux's sense, so that the separation theorem, stated for ordinary nets, applies to every net (proof prerequisite)
- A page reducing reachability in an arbitrary ordinary net to reachability in nets that are connected and have at least one place and one transition, or to vector addition systems, since the separation theorem is stated for those nets (proof prerequisite)

## Sources

- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Reachability" (Mayr's proof of 1981, Kosaraju's simplification, and the book-length account of the proof).
- J. Esparza, "Decidability and complexity of Petri net problems – an introduction", in *Lectures on Petri Nets I: Basic Models*, Lecture Notes in Computer Science 1491, Springer, 1998, pp. 374–428, <https://archive.model.in.tum.de/um/bibdb/esparza/course.pdf>, Section 8 (decidability by Mayr and Kosaraju and the gap to the exponential-space lower bound).
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Section 3.2.3, paragraph "Reachability": Theorem 3.2.24 and the algorithm of two semi-decision procedures after it, pp. 65–66.
- J. Leroux, "The general vector addition system reachability problem by Presburger inductive invariants", *Logical Methods in Computer Science* 6(3:22), 2010, <https://arxiv.org/abs/1009.1076>, Corollary 8.4 and the algorithm in Section 9.
