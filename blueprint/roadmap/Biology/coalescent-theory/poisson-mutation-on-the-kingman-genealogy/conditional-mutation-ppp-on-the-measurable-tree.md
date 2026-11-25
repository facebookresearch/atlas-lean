# Conditional Poisson process of mutations on the local trees of the ancestral recombination graph

Consider the [ancestral recombination graph](../pairwise-differences-under-poisson-mutation/marked-whole-chromosome-arg-on-0-1-with-homogene.md) of $n$ samples on $[0, 1)$. Label the branches of the local tree $G_x$ at position $x$ by their sets $D \subseteq [n]$ of descendant samples, with lengths $\ell_D(x, \omega)$, which are jointly measurable in $(x, \omega)$ by [the finiteness of the breakpoints](../pairwise-differences-under-poisson-mutation/finitely-many-breakpoints-and-a-jointly-measurab.md). Let $\theta \ge 0$ be the mutation rate for the whole chromosome.

Given the graph, mutations form a [Poisson point process](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md) on $[0, 1) \times \{D\} \times [0, \infty)$ with intensity

$$\frac{\theta}{2}\, \mathbf{1}\{0 < s < \ell_D(x, \omega)\}\, dx\, ds,$$

whose total mass $\frac{\theta}{2} \int_0^1 L_x\, dx$, with $L_x$ the total length of $G_x$, is finite almost surely. The conditional law is given by a measurable kernel from the graph to point configurations. For $n = 2$, with $T_x$ the coalescence time at $x$, the number $S$ of segregating sites satisfies

$$S \mid \text{graph} \sim \operatorname{Poisson}\Bigl(\theta \int_0^1 T_x\, dx\Bigr).$$

## Depends on

- [Finitely many breakpoints and a jointly measurable local-tree field](../pairwise-differences-under-poisson-mutation/finitely-many-breakpoints-and-a-jointly-measurab.md)
- [Poisson point process with finite intensity](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)
- [Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction](../pairwise-differences-under-poisson-mutation/marked-whole-chromosome-arg-on-0-1-with-homogene.md)

## Expansion

1. Measurability of the kernel in $\omega$, from the joint measurability of the branch lengths.
2. Finiteness of the total mass.
3. For $n = 2$, the conditional Poisson law of $S$, with conditional mean $\theta \int_0^1 T_x\, dx$.

## Sources

- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://doi.org/10.1007/978-0-387-78168-6> (mutation on genealogies).
