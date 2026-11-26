# Characterization of unbounded Petri nets

An ordinary [Petri net](place-transition-petri-nets.md) $(N, M_0)$ is unbounded (see [boundedness](boundedness-and-safeness.md)) if and only if there are a reachable marking $M$ and a sequence of transitions $\sigma$ with $M [\sigma\rangle M + L$ for some nonzero marking $L$, where markings are added placewise. Such a $\sigma$ is a *token generator*.

## Depends on

- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)
- [Place/transition Petri nets](place-transition-petri-nets.md)

## Proof depends on

- [Monotonicity lemma for Petri net firing sequences](decision-procedures/monotonicity-lemma-for-firing-sequences.md)
- [König's lemma for finitely branching graphs](decision-procedures/konig-s-lemma-for-finitely-branching-graphs.md)
- [Dickson's lemma for finite products of well-quasi-orders](decision-procedures/dickson-s-lemma.md)

## Sources

- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Boundedness".
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.3 and its proof (the monotonicity lemma, König's lemma and Dickson's lemma), pp. 49–50.
