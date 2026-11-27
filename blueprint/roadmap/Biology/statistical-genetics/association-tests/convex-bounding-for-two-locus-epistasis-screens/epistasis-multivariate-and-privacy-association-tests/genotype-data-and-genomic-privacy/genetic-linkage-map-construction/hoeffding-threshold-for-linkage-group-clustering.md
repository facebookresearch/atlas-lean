# Hoeffding threshold for splitting markers into linkage groups

**Setting.** In a doubled-haploid mapping population of $n$ individuals, markers $l_i$ and $l_j$ on different linkage groups (different chromosomes, or far apart) segregate independently, so each individual is recombinant with probability $P_{i,j} = \tfrac12$ and the recombinant count $d_{i,j}$ (Hamming distance of the two genotype rows) is $\mathrm{Binomial}(n, \tfrac12)$.

**Proposition.** For $0 \le \delta < n/2$,

$$\Pr\big(d_{i,j} \le \delta\big) \;\le\; \exp\!\Big(-\frac{2\,(n/2-\delta)^2}{n}\Big).$$

Hence, given a tolerated error probability $\epsilon$, choosing $\delta$ as the solution of

$$-\frac{2\,(n/2-\delta)^2}{n} = \log \epsilon$$

guarantees that a pair of markers from different linkage groups has $d_{i,j} < \delta$ with probability at most $\epsilon$.

**Clustering rule.** Build the complete graph on the markers with edge weights $d_{i,j}$, delete every edge with $d_{i,j} \ge \delta$, and take the connected components (equivalently, cut the minimum spanning tree at edges of weight $\ge \delta$) as linkage groups.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Expansion

The bound is Hoeffding's inequality for a sum of $n$ independent indicators with mean $\tfrac12$: the deviation $n/2 - d_{i,j}$ below the mean exceeds $t$ with probability at most $e^{-2t^2/n}$. Linked markers in dense maps have recombination fractions well below $0.05$, so their counts lie far below $\delta$, and the component structure is insensitive to the precise choice of $\epsilon$ over a wide range (the authors use $\epsilon = 10^{-5}$ by default and recommend $\epsilon < 10^{-4}$).

## Sources

- Y. Wu, P. R. Bhat, T. J. Close, S. Lonardi, "Efficient and accurate construction of genetic linkage maps from the minimum spanning tree of a graph", PLoS Genetics 4(10) (2008) e1000212, Materials and Methods (clustering markers into linkage groups) and Theorem 1 of Supplementary Text S1, <https://doi.org/10.1371/journal.pgen.1000212>, PMCID PMC2556103.
