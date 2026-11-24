# Rate matrices of the coalescent in an allelic background with a frozen frequency path

In the [coalescent in an allelic background with a given frequency path](coalescent-in-an-allelic-background-with-a-given.md), fix the frequency path $x(t)$ of the selected allele on a time window on which $\delta \le x(t) \le 1 - \delta$ for some $\delta > 0$, with $x$ piecewise continuous. The time-indexed matrices $Q(t)$ on the states (assignment of the lineages to backgrounds, partition of the sample) are rate matrices for each $t$: their off-diagonal entries are nonnegative and their rows sum to $0$. As functions of $t$ they are piecewise continuous, and their entries are bounded uniformly on the window by a constant depending only on $\delta$, the recombination rate $\rho$, the mutation rates $\theta$ and the sample size.

## Expansion

1. The row sums and the signs of the entries, from the rates of the background coalescent.
2. The uniform bound, from $1/x(t) \le 1/\delta$ and $1/(1 - x(t)) \le 1/\delta$.
3. Piecewise continuity from that of $x$.

Prerequisites:

- [Structured coalescent for n lineages with a general migration matrix](../structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)

## Sources

- N. L. Kaplan, T. Darden and R. R. Hudson, The coalescent process in models with selection, *Genetics* 120 (1988), 819–829 (background coalescent).
