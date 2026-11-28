# Degree distribution and limit laws of the split-and-drift random graph

**Setting.** $G_{n,r_n}$ is the stationary random graph on $n$ vertices under vertex duplication at rate $1$ and edge removal at rate $\rho_n$, with $r_n = \frac{n-1}{2}\rho_n$ ([coalescent construction and regimes](coalescent-construction-and-regimes-of-the-split-and-drift-random-graph.md)). Let $D_n$ be the degree of a fixed vertex, $|E_n|$ the number of edges and $\#\mathrm{cc}_n$ the number of connected components.

**Theorem (degree distribution).** For $k \in \{0,\dots,n-1\}$,

$$\mathbb{P}(D_n = k) = \frac{2r_n(2r_n+1)}{(n+2r_n)(n-1+2r_n)}\,(k+1)\prod_{i=1}^{k}\frac{n-i}{n-i+2r_n-1}.$$

**Theorem (rescaled degree).**

1. If $r_n \to r > 0$, then $D_n/n \to \mathrm{Beta}(2, 2r)$ in distribution.
2. If $1 \ll r_n \ll n$, then $D_n/(n/r_n)$ converges to a size-biased exponential variable with parameter $2$ (density $4x e^{-2x}$).
3. If $2r_n/n \to \rho > 0$, then $D_n + 1$ converges to a size-biased geometric variable with parameter $\rho/(1+\rho)$.

**Theorem (connected components, intermediate regime).** If $1 \ll r_n \ll n$,

$$\frac{r_n}{2} + o_P(r_n) \le \#\mathrm{cc}_n \le 2r_n\log n + o_P(r_n\log n).$$

**Theorem (edges, sparse regime).** If $r_n = \omega(n)$, then $d_{\mathrm{TV}}\big(|E_n|, \mathrm{Poisson}(\lambda_n)\big) \to 0$ with $\lambda_n = \mathbb{E}|E_n| \sim n^2/(2r_n)$; if moreover $r_n = o(n^2)$, then $(|E_n| - \lambda_n)/\sqrt{\lambda_n} \to N(0,1)$.

## Depends on

- [Coalescent construction and regimes of the split-and-drift random graph](coalescent-construction-and-regimes-of-the-split-and-drift-random-graph.md)

## Expansion

In the coalescent construction, the neighbors of a vertex $i$ are the vertices whose lineage joins the ancestral lineage of $i$ before an edge-removal event separates them; tracing the block of $i$ backward gives a forest of rooted trees with marked vertices whose law yields the product formula, a beta-binomial type law with a size-biasing factor $k+1$. Its scaling limits follow by Stirling-type estimates: in the dense-to-intermediate range the product behaves like $(1-k/n)^{2r_n}$. The component bounds count *founder* pairs, pairs that never inherited an ancestor other than themselves, which approximately mark the separations created by drift. The Poisson approximation uses the Stein–Chen method for positively related Bernoulli variables: edge indicators are positively related because they are monotone functions of independent processes evaluated at an independent time, so the total-variation error is controlled by $\mathrm{Var}|E_n| - \lambda_n$, which is small when $r_n \gg n$.

## Sources

- François Bienvenu, Florence Débarre and Amaury Lambert, "The split-and-drift random graph, a null model for speciation", *Stochastic Process. Appl.* 129(6) (2019), 2010–2048. <https://doi.org/10.1016/j.spa.2018.06.009>
- Preprint version (the locators in this item follow its numbering): François Bienvenu, Florence Débarre and Amaury Lambert, "The split-and-drift random graph, a null model for speciation", arXiv:1706.01015 (2017), Section 4 (Theorems 4.1–4.2, Definition 4.3), Section 5 (Theorem 5.1, Definition 5.2) and Section 6 (Theorem 6.1, Lemmas 6.2–6.3, Proposition 6.5), <https://doi.org/10.48550/arXiv.1706.01015>.
