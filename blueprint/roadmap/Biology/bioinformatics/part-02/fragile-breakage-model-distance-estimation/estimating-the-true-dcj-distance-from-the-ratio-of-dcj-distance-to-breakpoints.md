# Estimating the true DCJ distance from the ratio of DCJ distance to breakpoints

**Setting (fragile breakage model).** Genomes $P_n$ and $Q_n$ consist of $n$ solid regions separated by $n$ fragile regions (adjacencies; linear chromosomes are circularised by one artificial adjacency). $Q_n$ is obtained from $P_n$ by $k$ random double-cut-and-join operations (DCJs), each choosing two adjacencies uniformly at random and rejoining them in one of the two other ways. In the breakpoint graph $G(P_n,Q_n)$ (black adjacencies of $P$, red adjacencies of $Q$), an $\ell$-cycle is an alternating cycle with $\ell$ black edges, and $c_\ell$ counts them. Only non-trivial cycles ($\ell\ge 2$) are observable from the synteny blocks of $P,Q$: the observable quantities are $c_\ell$ for $\ell\ge2$, the number of broken fragile regions $b=\sum_{\ell\ge2}\ell c_\ell$ and the DCJ distance $d=b-\sum_{\ell\ge2}c_\ell$, while $n$, $c_1$ and the true distance $k$ are hidden.

Let $p_\ell=e^{-\gamma\ell}(\gamma\ell)^{\ell-1}/\ell!$ be the asymptotic fraction of edges in $\ell$-cycles from [Borel law for breakpoint-graph cycles under random DCJs](borel-law-for-breakpoint-graph-cycles-under-random-dcjs.md), with $k=\lfloor\gamma n/2\rfloor$.

**Corollary 1.** $\dfrac bn=1-e^{-\gamma}+o_p(1)$.

**Corollary 2.** $\dfrac dn=1-\sum_{\ell\ge1}\dfrac{p_\ell}{\ell}+o_p(1)$.

**Estimator.** Consequently

$$\frac db\approx\frac{1-\sum_{\ell\ge1}\frac{e^{-\gamma\ell}(\gamma\ell)^{\ell-1}}{\ell\cdot\ell!}}{1-e^{-\gamma}},$$

an increasing function of $\gamma$ taking each value in $[1/2,1)$ once. Solving it for $\gamma$ (e.g. by bisection) from the observed $d/b$ gives $\hat n=b/(1-e^{-\hat\gamma})$ and $\hat k=\hat\gamma\hat n/2$. The value $\gamma=1$ corresponds to $d/b\approx0.79$: below it the process is in the parsimony phase and $\hat k\approx d$. An alternative uses short cycles only: $b/\sum_{\ell=2}^{m}\ell c_\ell$ estimates $f_m(\gamma)=(1-e^{-\gamma})/\sum_{\ell=2}^{m}p_\ell$, which is also increasing in $\gamma$.

## Expansion

Corollary 1 follows from $b=n-c_1$ and $c_1/n\to p_1=e^{-\gamma}$, the probability that an adjacency is never touched by any of the $k$ DCJs. Corollary 2 follows from $d=n-\sum_{\ell\ge1}c_\ell$: the finitely many short-cycle terms are controlled by Theorem 1, and the contribution of cycles longer than $M$ is at most $n/M$, which is made small before letting $n\to\infty$. The ratio $d/b$ eliminates the unknown $n$, which is why it is the statistic to invert; simulations with $n=1000$ show the $d/b$ estimator is reliable for $\gamma<2$, and the short-cycle variant with $m=6$ stays within 10% relative error in 95% of runs for $\gamma<2.5$. Beyond that, the ratio flattens and small fluctuations move $\hat\gamma$ a lot.

## Depends on

- [Borel law for breakpoint-graph cycles under random DCJs](borel-law-for-breakpoint-graph-cycles-under-random-dcjs.md)
- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Sources

- Alexeev N, Alekseyev MA, "Estimation of the true evolutionary distance under the fragile breakage model" (2017), Corollary 1, Corollary 2, equations (3) and (4) and the estimation algorithm, <https://doi.org/10.1186/s12864-017-3733-3>, PMCID PMC5461553.
