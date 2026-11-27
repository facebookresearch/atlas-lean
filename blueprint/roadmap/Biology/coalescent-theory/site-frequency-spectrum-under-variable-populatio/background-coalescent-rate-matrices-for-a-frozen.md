# Rate matrices of the coalescent in an allelic background with a frozen frequency path

Fix a piecewise continuous frequency path $x(t)$ of a selected allele $A$ on a time window on which $\delta \le x(t) \le 1 - \delta$ for some $\delta > 0$. On the states (assignment of the lineages to backgrounds $A$, $B$, partition of the sample) let $Q(t)$ have the rates, with $x = x(t)$: a lineage moves from $A$ to $B$ at rate $\frac{\theta_{BA}}{2}\frac{1-x}{x} + \frac{\rho}{2}(1-x)$ and from $B$ to $A$ at rate $\frac{\theta_{AB}}{2}\frac{x}{1-x} + \frac{\rho}{2}x$, and each pair in $A$ coalesces at rate $1/x$ and each pair in $B$ at rate $1/(1-x)$; these are the backward rates of the [coalescent in an allelic background with a given frequency path](coalescent-in-an-allelic-background-with-a-given.md). The matrices $Q(t)$ are rate matrices for each $t$: their off-diagonal entries are nonnegative and their rows sum to $0$. As functions of $t$ they are piecewise continuous, and their entries are bounded uniformly on the window by a constant depending only on $\delta$, the recombination rate $\rho$, the mutation rates $\theta$ and the sample size.

## Proof depends on

- [Structured coalescent for n lineages with a general migration matrix](../structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)

## Expansion

1. The row sums and the signs of the entries, from the rates of the background coalescent.
2. The uniform bound, from $1/x(t) \le 1/\delta$ and $1/(1 - x(t)) \le 1/\delta$.
3. Piecewise continuity from that of $x$.

## Sources

- N. L. Kaplan, T. Darden and R. R. Hudson, The coalescent process in models with selection, *Genetics* 120 (1988), 819–829 (background coalescent).
