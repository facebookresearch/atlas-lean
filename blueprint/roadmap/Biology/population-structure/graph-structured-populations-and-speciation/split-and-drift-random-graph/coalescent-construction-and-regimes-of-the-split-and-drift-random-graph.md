# Coalescent construction and regimes of the split-and-drift random graph

**Model.** As a null model for speciation, the vertices $V = \{1,\dots,n\}$ are populations and edges mean that two populations can still interbreed. The graph evolves by

- **vertex duplication (split):** each vertex duplicates at rate $1$, choosing another vertex $j$ uniformly and replacing it by a copy of itself: $j$ loses its edges and is linked to $i$ and to all neighbors of $i$;
- **edge removal (drift):** each edge disappears at rate $\rho$.

This irreducible Markov chain on graphs has a unique stationary law; the **split-and-drift random graph** $G_{n,r_n}$ is a sample from it, parametrized by $r_n = \frac{n-1}{2}\rho_n$.

**Coalescent representation.** Let $(K_t)$ be a Kingman coalescent on $V$ with blocks $\pi_t(i)$, let the lineage of a pair $\{i,j\}$ be $\{(t,\{\pi_t(i),\pi_t(j)\}) : t < T_{\{ij\}}\}$ up to the coalescence time $T_{\{ij\}}$, and put a Poisson process of intensity $r_n$ on the genealogy of pairs (lineages that have merged share their points). Then $G_{n,r_n}$ has the law of the graph whose edges are the pairs whose lineage received no point.

**Moments.** For distinct vertices $i,j,k,\ell$, with $D_n$ the degree of a vertex, $|E_n|$ the number of edges and $X_{n,k}$ the number of $k$-cliques:

$$\mathbb{P}(i \sim j) = \frac{1}{1+r_n}, \qquad \mathbb{E}(D_n) = \frac{n-1}{1+r_n}, \qquad \mathbb{E}|E_n| = \binom n2\frac{1}{1+r_n},$$

$$\mathrm{Cov}(\mathbf{1}_{i\sim j}, \mathbf{1}_{i\sim k}) = \frac{r_n}{(3+2r_n)(1+r_n)^2}, \qquad \mathrm{Cov}(\mathbf{1}_{i\sim j}, \mathbf{1}_{k\sim \ell}) = \frac{2r_n}{(1+r_n)^2(3+r_n)(3+2r_n)},$$

$$\mathrm{Var}(D_n) = \frac{r_n(n-1)(1+2r_n+n)}{(1+r_n)^2(3+2r_n)}, \qquad \mathbb{E}(X_{n,k}) = \binom nk\Big(\frac{1}{1+r_n}\Big)^{k-1}.$$

Consequently the clique number satisfies $\kappa_n \le \log(r_n)\,n/r_n$ a.a.s. when $r_n \to \infty$ with $r_n = o(n)$.

**Theorem (regimes).** As $n \to \infty$:

1. $\mathbb{P}(G_{n,r_n}\text{ complete}) \to 1$ if $r_n = o(1/n)$, $\to 0$ if $r_n = \omega(1/n)$, and stays in $(0,1)$ if $r_n = \Theta(1/n)$;
2. dense regime: if $r_n = o(1)$, $\mathbb{P}(D_n = n-1) \to 1$;
3. sparse regime: if $r_n = \omega(n)$, $\mathbb{P}(D_n = 0) \to 1$;
4. $\mathbb{P}(G_{n,r_n}\text{ empty}) \to 0$ if $r_n = o(n^2)$, $\to 1$ if $r_n = \omega(n^2)$, and stays in $(0,1)$ if $r_n = \Theta(n^2)$.

Between the dense and sparse regimes lies an intermediate regime $1 \ll r_n \ll n$ with degrees of order $n/r_n$.

## Depends on

- [Kingman's coalescent](../../../coalescent-theory/coalescents/merger-rate-dirac-zero.md)

## Expansion

Backward in time, the replacement of $j$ by a copy of $i$ is a coalescence of their ancestral lineages, so the genealogy of vertices is that of a Moran model, and after rescaling a Kingman coalescent; $\{i,j\}$ is an edge iff no edge-removal event hit the ancestral pair before the two lineages merged. Since a pair coalesces at rate $1$ and is killed at rate $r_n$ in these units, $\mathbb{P}(i \sim j) = 1/(1+r_n)$; covariances come from the times during which two pairs share an ancestral pair. A $k$-clique requires $k-1$ successive merger intervals to be free of removals, giving $(1+r_n)^{-(k-1)}$. The transitions follow from first- and second-moment arguments and the exact formula $\mathbb{P}(D_n = n-1) = \Gamma(2+2r_n)\Gamma(n+1)/\Gamma(n+1+2r_n)$.

## Sources

- François Bienvenu, Florence Débarre and Amaury Lambert, "The split-and-drift random graph, a null model for speciation", *Stochastic Process. Appl.* 129(6) (2019), 2010–2048. <https://doi.org/10.1016/j.spa.2018.06.009>
- Preprint version (the locators in this item follow its numbering): François Bienvenu, Florence Débarre and Amaury Lambert, "The split-and-drift random graph, a null model for speciation", arXiv:1706.01015 (2017), Section 1.1 (model), Section 2 (Lemma 2.2, Propositions 2.3–2.4) and Section 3 (Propositions 3.1, 3.3, 3.5, 3.7, Corollaries 3.2, 3.4, 3.6, 3.8, Theorem 3.10), <https://doi.org/10.48550/arXiv.1706.01015>.
