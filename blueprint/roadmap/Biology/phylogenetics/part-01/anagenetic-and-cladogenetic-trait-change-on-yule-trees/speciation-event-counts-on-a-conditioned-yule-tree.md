# Speciation event counts on a conditioned Yule tree

**Setting.** Let a Yule (pure-birth) tree with rate $\lambda$ be conditioned to have $n$ extant tips. Define

- $\Upsilon$: the number of speciation events on the lineage from the origin of the tree to a uniformly chosen tip (its depth in edges);
- $\upsilon$: the number of speciation events from the origin to the most recent common ancestor of two uniformly chosen distinct tips, excluding that ancestor.

Both are topological and do not depend on $\lambda$. Write $H_n=\sum_{i=1}^n 1/i$, $H_{n,2}=\sum_{i=1}^n 1/i^2$ and

$$b_{n,y}=\frac{1}{y+1}\cdot\frac{2}{y+2}\cdots\frac{n}{y+n}=\frac{\Gamma(n+1)\Gamma(y+1)}{\Gamma(n+y+1)}.$$

**Lemma 2.1.** The two sampled tips coalesce at the $k$-th speciation event (counting forward) with probability

$$\pi_{k,n}=\frac{2(n+1)}{(n-1)(k+1)(k+2)}, \qquad k=1,\dots,n-1.$$

**Theorem 2.1.** For $s>0$,

$$\mathbb{E}\bigl[s^{\Upsilon}\bigr]=\frac{1}{n\,b_{n-1,2s-1}},$$

and, for $n\ge 2$,

$$\mathbb{E}\bigl[s^{\upsilon}\bigr]=\frac{1}{(n-1)(3-2s)}\Bigl((n+1)-\frac{2}{n\,b_{n-1,2s-1}}\Bigr)\quad(s\neq 3/2), \qquad \mathbb{E}\bigl[(3/2)^{\upsilon}\bigr]=\frac{n+1}{n-1}\Bigl(H_{n+1}-\frac{3}{2}\Bigr).$$

The value at $s=3/2$ is the limit $s\to3/2$ of the general formula (for $n=3$ it is $7/6$, which exact enumeration confirms); the source's eq. (11) prints $\frac{2(n+1)}{n-1}\bigl(H_{n+1}-\frac53\bigr)$, a slip.

**Moments.**

$$\mathbb{E}[\Upsilon]=2H_n-2, \qquad \mathbb{E}[\upsilon]=\frac{4(n-H_n)}{n-1}-2\to 2,$$

$$\operatorname{Var}[\Upsilon]=2\bigl(H_n-1-2(H_{n,2}-1)\bigr)\sim 2\ln n,$$

$$\operatorname{Var}[\upsilon]=6-\frac{8(n+1)}{(n-1)^2}(H_n-1)^2-\frac{4(H_n-1)}{n-1}+\frac{8(H_{n,2}-1)}{n-1}\to 6.$$

If each speciation event is independently marked with probability $p$, the marked counts have means $p\,\mathbb{E}[\Upsilon]$ and $p\,\mathbb{E}[\upsilon]$. The expected total area $\sum_{i<j}d(i,j)$ of the tree, with $d$ the edge-count distance, is $2n(n+1)H_n-4n^2\sim 2n^2\ln n$.

## Expansion

$\Upsilon=\sum_{i=1}^{n-1}\mathbf 1_i$, where $\mathbf 1_i$ indicates that the $i$-th speciation event lies on the chosen lineage; just before that event $i+1$ lineages remain, the merging pair is uniform among $\binom{i+1}{2}$, and exactly $i$ pairs involve the tracked lineage, so $\mathbb{P}(\mathbf 1_i=1)=2/(i+1)$, and the indicators are independent. Hence $\mathbb{E}[s^{\Upsilon}]=\prod_{i=1}^{n-1}\bigl(1+\tfrac{2(s-1)}{i+1}\bigr)$, which equals $1/(n\,b_{n-1,2s-1})$. For $\upsilon$, condition on the index $k$ of the coalescence event via Lemma 2.1; the speciation events above it lie on a single lineage of the tree as it was when it had $k$ lineages, and averaging the resulting depth generating function against $\pi_{k,n}$ gives the stated closed form (Appendix A). Variances come from second derivatives at $s=1$.

## Sources

- Krzysztof Bartoszek, "Quantifying the effects of anagenetic and cladogenetic evolution", arXiv:1305.2378 (2013), Section 2 (Lemma 2.1, the derivations of the means, Theorem 2.1, the variance formulas and the connection to total tree area), Appendix A (proof of Theorem 2.1), <https://doi.org/10.48550/arXiv.1305.2378>. Published version: Mathematical Biosciences 254 (2014), 42–57, <https://doi.org/10.1016/j.mbs.2014.06.002>; locators above refer to the arXiv version.
