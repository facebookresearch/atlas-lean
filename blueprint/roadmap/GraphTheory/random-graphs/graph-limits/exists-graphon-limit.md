# Lovász–Szegedy limit theorem

Every convergent sequence of nonempty simple graphs $G_n$ has a graphon limit: there is a graphon $W$ (symmetric, measurable, values in $[0, 1]$) such that

$$t(F, G_n) \to t(F, W) \quad \text{for every simple graph } F.$$

Lovász and Szegedy prove more: the limits of $t(\cdot, G_n)$ are exactly the graph parameters of the form $t(\cdot, W)$, and also exactly the normalized, multiplicative, reflection-positive parameters.

Their proof passes to a subsequence whose weakly regular partitions refine each other with converging density matrices, builds $W$ as the almost-everywhere limit of the corresponding step functions (a martingale), and compares densities with the counting lemma.

## Informally uses

- [Weak regularity lemma (Frieze–Kannan)](exists-cut-norm-sub-partition-average-le.md): weakly $\varepsilon$-regular partitions of each graph in the sequence, in the proof of Lemma 5.1. Lovász and Szegedy use the equitable variant of the weak regularity lemma (their Lemma 4.2, classes of almost equal size); the linked page is the Borgs et al. form (Lemma 2.4).
- [Counting lemma](abs-hom-density-sub-hom-density-le.md): inequality (7), to compare $t(F, G'_m)$ with the densities of the partition averages.

## Background

- [Convergent graph sequence](is-convergent-graph-sequence.md) and [Homomorphism density in a graphon](graphon-hom-density.md): the notions in the statement.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, Theorem 2.2, (a) ⇒ (b); proof in §5.4.
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Theorem 3.1.
