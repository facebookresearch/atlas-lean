# Linear-time skewness of the mean pairwise distance

**Setting.** Let $T$ be a rooted phylogenetic tree with edge set $E$, $n=|E|$, nonnegative edge weights $w_e$, and tip set $S$ with $s=|S|$. For tips $u,v$ let $\mathrm{cost}(u,v)$ be the total weight of the path between them. For $R\subseteq S$ with $|R|=r\ge 2$, the *mean pairwise distance* is

$$\mathrm{MPD}(T,R)=\frac{2}{r(r-1)}\sum_{\{u,v\}\subseteq R,\ u\ne v}\mathrm{cost}(u,v).$$

Let $R$ be drawn uniformly from the $\binom{s}{r}$ subsets of exactly $r$ tips, and write $\mu(T,r)$, $\sigma^2(T,r)$ for the mean and variance of $\mathrm{MPD}(T,R)$. The skewness is

$$\mathrm{sk}(T,r)=\frac{\mathbb E[\mathrm{MPD}^3(T,R)]-3\mu(T,r)\sigma^2(T,r)-\mu(T,r)^3}{\sigma^3(T,r)}.$$

**Mean.** Every unordered pair of distinct tips lies in $R$ with the same probability, so

$$\mu(T,r)=\binom{s}{2}^{-1}\sum_{\{u,v\}\subseteq S}\mathrm{cost}(u,v),$$

independent of $r$.

**Theorem 3 (linear-time skewness).** For every $r\le s$, $\mathrm{sk}(T,r)$ can be computed in $\Theta(n)$ time.

The proof rests on two lemmas. **Lemma 1:** a fixed family of path-cost aggregates (for example the total cost $\sum_{\{u,v\}}\mathrm{cost}(u,v)$, the total cubed cost, and for every edge $e$ the sums of $\mathrm{cost}(u,v)$ and $\mathrm{cost}^2(u,v)$ over the pairs whose path contains $e$) can all be computed in $O(n)$ total time by a constant number of bottom-up and top-down scans plus one divide-and-conquer pass. **Lemma 2:** $\mathbb E[\mathrm{MPD}^3(T,R)]$ is an explicit linear combination of these aggregates with coefficients depending only on $r$ and $s$, hence computable in $\Theta(n)$ time.

## Expansion

Expanding the cube writes $\mathbb E[\mathrm{MPD}^3]$ as $\big(\tfrac{2}{r(r-1)}\big)^3$ times a sum over ordered triples of tip pairs of $\mathrm{cost}(u,v)\mathrm{cost}(x,y)\mathrm{cost}(z,q)$, weighted by the probability that all tips involved fall in $R$. That probability depends only on the number $m\in\{2,\dots,6\}$ of distinct tips among the three pairs, namely $\binom{s-m}{r-m}/\binom{s}{r}$. Grouping the triples by how the three pairs overlap reduces each group to one of the edge-indexed aggregates, which a tree traversal accumulates edge by edge. Together with the previously known linear-time mean and variance, this yields the skewness, which the authors use to correct the normal approximation of MPD $P$ values.

## Sources

- Tsirogiannis C, Sandel B, "Computing the skewness of the phylogenetic mean pairwise distance in linear time", Algorithms Mol Biol 2014 Jun 14;9:15, Equation (1), Table 1, Lemmas 1-2 and Theorem 3, <https://doi.org/10.1186/1748-7188-9-15>, PMCID PMC4105894.
