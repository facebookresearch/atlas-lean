# Pybus–Harvey gamma statistic

Let a reconstructed ultrametric phylogeny have $n \ge 3$ tips, and let $g_k > 0$ ($k = 2, \dots, n$) be the internode interval during which exactly $k$ lineages are present. Set

$$T = \sum_{j=2}^{n} j\, g_j, \qquad T_i = \sum_{k=2}^{i} k\, g_k \quad (i = 2, \dots, n - 1).$$

The gamma statistic is

$$\gamma = \frac{\dfrac{1}{n - 2}\displaystyle\sum_{i=2}^{n-1} T_i - \dfrac{T}{2}}{T\sqrt{\dfrac{1}{12(n - 2)}}}.$$

Under a constant-rate pure-birth (Yule) process with speciation rate $\lambda > 0$, the scaled intervals $j g_j$ ($j = 2, \dots, n$) are independent $\mathrm{Exp}(\lambda)$ variables; consequently $(T_2/T, \dots, T_{n-1}/T)$ has the law of the order statistics of $n - 2$ independent uniform variables on $(0, 1)$, and $\gamma$ is approximately standard normal for large $n$.

Properties:

- $\gamma$ does not depend on the time unit (it is invariant under rescaling all $g_k$ by a common factor);
- $\gamma < 0$ when internal nodes are concentrated towards the root, the signature of an early burst or a slowdown of lineage accumulation, and $\gamma > 0$ when they are concentrated towards the tips (accelerating accumulation or high extinction).

## Expansion

With $k$ lineages present, the waiting time to the next split under the Yule process is exponential with rate $k\lambda$, so $k g_k \sim \mathrm{Exp}(\lambda)$, independently across $k$. Partial sums of $n - 1$ independent exponentials, divided by their total, are distributed as uniform order statistics; the average of $n - 2$ such values has mean $1/2$ and variance $1/(12(n - 2))$, which is the centring and scaling in $\gamma$. Because $\gamma$ summarizes the whole tree, a recent rate change can mask an early burst; in the extant cetacean phylogeny (87 of 89 species), $\gamma$ was recomputed after excluding the most recent 10 million years, and neither version supported an early rapid radiation.

## Sources

- M. E. Steeman, M. B. Hebsgaard, R. E. Fordyce, et al., "Radiation of extant cetaceans driven by restructuring of the oceans", Systematic Biology (2009), METHODS (gamma statistic, after Pybus and Harvey 2000) and RESULTS AND DISCUSSION, "Testing Hypotheses on Evolutionary Drivers", <https://doi.org/10.1093/sysbio/syp060> (PMC2777972).
- O. G. Pybus, P. H. Harvey, "Testing macro-evolutionary models using incomplete molecular phylogenies", Proceedings of the Royal Society B (2000), definition of the statistic.
