# Borel law for breakpoint-graph cycles under random DCJs

**Setting (fragile breakage model).** Genomes $P_n$ and $Q_n$ consist of $n$ solid regions separated by $n$ fragile regions (adjacencies; linear chromosomes are circularised by one artificial adjacency). $Q_n$ is obtained from $P_n$ by $k$ random double-cut-and-join operations (DCJs), each choosing two adjacencies uniformly at random and rejoining them in one of the two other ways. In the breakpoint graph $G(P_n,Q_n)$ (black adjacencies of $P$, red adjacencies of $Q$), an $\ell$-cycle is an alternating cycle with $\ell$ black edges, and $c_\ell$ counts them. Only non-trivial cycles ($\ell\ge 2$) are observable from the synteny blocks of $P,Q$: the observable quantities are $c_\ell$ for $\ell\ge2$, the number of broken fragile regions $b=\sum_{\ell\ge2}\ell c_\ell$ and the DCJ distance $d=b-\sum_{\ell\ge2}c_\ell$, while $n$, $c_1$ and the true distance $k$ are hidden.

**Theorem 1.** If $k=\lfloor\gamma n/2\rfloor$ for fixed $\gamma>0$, then for every fixed $\ell\ge1$, as $n\to\infty$,

$$\frac{\ell\,c_\ell}{n}=p_\ell+O_p\!\big(n^{-1/2}\big),\qquad p_\ell=\frac{e^{-\gamma\ell}(\gamma\ell)^{\ell-1}}{\ell!}.$$

**Lemma 1.** The number $\tilde c_\ell$ of $\ell$-cycles produced entirely by $\ell-1$ merging DCJs has mean $\mathbb E\tilde c_\ell=\frac{n}{\ell}\,p_\ell+O(1)$. **Lemma 2.** $\operatorname{Var}\tilde c_\ell=O(n)$. **Lemma 3.** Each DCJ of the transformation $\mathcal D$ of $P_n$ into $Q_n$ merges two cycles, splits one cycle into two, or preserves the cycle structure. For a positive integer $M$, call a splitting DCJ $M$-splitting if it splits some $m$-cycle into an $i$-cycle and an $(m-i)$-cycle for some $i\le M$, and a preserving DCJ $M$-preserving if it operates on an $m$-cycle for some $m\le M$. Then (i) the number of $M$-splitting DCJs in $\mathcal D$ is stochastically dominated by a Poisson random variable with parameter $\gamma M/2$, and (ii) the number of $M$-preserving DCJs in $\mathcal D$ is stochastically dominated by a Poisson random variable with parameter $\gamma M^2/4$. As used in the proof of Theorem 1, $c_\ell-\tilde c_\ell$ is at most twice the number of $\ell$-splitting and $\ell$-preserving DCJs, so $c_\ell-\tilde c_\ell=O_p(1)$.

**Borel distribution and the parsimony phase.** For $\gamma<1$, $(p_\ell)_{\ell\ge1}$ is the Borel distribution with parameter $\gamma$: the length of the cycle containing a random black edge is asymptotically Borel. Moreover $1-\sum_{\ell\ge1}p_\ell/\ell=\gamma/2$ for $\gamma<1$, so $d=k(1+o(1))$: the DCJ distance is asymptotically exact (the parsimony phase).

## Expansion

Choose a set $A$ of $\ell$ black edges. There are $2^{\ell-1}(\ell-1)!$ ways to arrange them into an alternating $\ell$-cycle, and $\ell^{\ell-2}$ ways to build a given $\ell$-cycle from $\ell-1$ merging DCJs (a Cayley-type count). Placing those $\ell-1$ operations among the $k$ steps and letting the other $k-\ell+1$ DCJs act on the remaining $n-\ell$ red edges gives the probability that $A$ is "proper"; multiplying by $\binom n\ell$ and using $(1-\ell/n)^{2k}\to e^{-\gamma\ell}$ yields Lemma 1. A second-moment computation over pairs of edge sets gives the variance bound, and Chebyshev's inequality turns mean and variance into Theorem 1. The structure is that of the Erdős–Rényi random graph with $n$ vertices and $k$ edges: merging DCJs act like edges joining components, cycles of length $\ell$ correspond to tree components of size $\ell$, and the giant component appears at $\gamma=1$, which is where breakpoint reuse becomes macroscopic. For $\gamma>1$ the source's simulations (Fig. 3) show the DCJ distance falling below $k$; this is a numerical observation of the source, not part of the statement.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Sources

- Alexeev N, Alekseyev MA, "Estimation of the true evolutionary distance under the fragile breakage model" (2017), Theorem 1, Lemmas 1-3 and the remark on the Borel distribution and parsimony phase, <https://doi.org/10.1186/s12864-017-3733-3>, PMCID PMC5461553.
