# Wiuf–Hein algorithm reproduces the joint law of local trees

This node covers a research programme on Wiuf and Hein's sequence-direction construction of the ancestral recombination graph under homogeneous recombination $\rho\,dx$. The algorithm moves along the sequence: at position $x$ it carries the ancestral graph of the material on $[0, x]$, and it adds a new recombination breakpoint and regrows the affected part of the graph according to a transition kernel. The target is the law equality, for every finite set of loci, between the joint law of the local trees produced by the algorithm and the finite-locus marginal law of the [continuum ancestral recombination graph](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md), not only a match of covariances.

## Expansion

A good expansion first fixes, from Wiuf and Hein (1999), the full carried state of the algorithm (the ancestral graph of the material $[0, x]$) and its transition kernel, then states and proves, as separate pages:

- for every finite locus set, the joint law of the local trees produced by the algorithm equals the finite-locus marginal of the [continuum ancestral recombination graph](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md);
- the two-locus case for a sample of two: the joint law of $(T_A, T_B)$ equals the law on the [path-form covariance page](covariance-coalescence-times.md), including the diagonal atom of the [two-locus coalescence times of a pair](two-locus-n-2-joint-law-of-t-a-t-b-is-diagonal-a.md).

Prerequisites:

- [Continuum ARG (homogeneous rho dx): finite-locus marginals and two-point law](continuum-arg-homogeneous-rho-dx-finite-locus-ma.md)
- [Candidate vs visible local-tree changes: expected counts (homogeneous rho dx)](../pairwise-differences-under-poisson-mutation/candidate-vs-visible-local-tree-changes-expected.md)

## Sources

- C. Wiuf and J. Hein, "Recombination as a point process along sequences", *Theoretical Population Biology*, 1999, <https://pubmed.ncbi.nlm.nih.gov/10366550/>
