# Biased voter models converge to a stochastic FKPP equation on metric graphs

Let $\Gamma = (V, E)$ be a finite metric graph whose edges $e$ are intervals. For each $n$ and each edge $e$, place demes along the interior of $e$ at spacing $1/L^e_n$, each holding $M^e_n$ individuals of type $1$ or type $0$. In the biased voter model, a type-$1$ individual (for example a mutant or cancer cell) and a type-$0$ individual at neighbouring demes replace each other at voter rates $a^{z,w}$, and type $1$ additionally takes over at selective rates $b^{z,w}$; demes adjacent to the same vertex are neighbours. Let $u^n_t(x)$ be the local type-$1$ frequency, interpolated to a continuous function on $\Gamma$.

**Theorem.** Suppose, as $n \to \infty$, $1/L^e \to 0$ uniformly, $4L^e/M^e \to \gamma_e/\alpha_e$, the voter rates are $a^{z,w} = 2C^n_{\tilde e, e} L^e/M^e$ with suitably converging vertex weights, the interior selection rates satisfy $2B^n_e M^e \to \beta_e$, and the selection rates at demes next to a vertex $v$ satisfy a scaling with limit $\hat\beta(v) \ge 0$. If $u^n_0 \to f_0$ in $\mathcal{C}_{[0,1]}(\Gamma)$, then $u^n$ converges in distribution in $D([0,\infty), \mathcal{C}_{[0,1]}(\Gamma))$ to the continuous weak solution of

$$
\partial_t u = \alpha_e\,\Delta u + \beta_e\,u(1-u) + \sqrt{\gamma_e\,u(1-u)}\;\dot W \quad \text{on the interior of each edge } e,
$$

with the vertex boundary condition

$$
\sum_{e \in E(v)} \alpha_e\,\partial_{e} u(v) = -\hat\beta(v)\,u(v)\,(1-u(v)) \qquad \text{for each } v \in V,
$$

where $\partial_e u(v)$ is the outward derivative along $e$ at $v$, $\dot W$ is space-time white noise, and $u(0) = f_0$.

## Depends on

- [Coalescing random walks dual to the voter model on a finite graph](../../../../coalescent-theory/structured-coalescent/coalescing-random-walks-dual-to-the-voter-moran.md)

## Expansion

The voter mechanism yields the Laplacian (random-walk migration), the selective bias the logistic drift, and the resampling within finite demes the Wright–Fisher noise $\sqrt{\gamma u(1-u)}$, with $\gamma_e$ determined by the ratio of sites per unit length to deme size. At a vertex, selection concentrated on a vanishing neighbourhood leaves a flux condition: Kirchhoff's law perturbed by a selective source $\hat\beta(v)u(1-u)$. The proof uses tightness from uniform heat kernel estimates and a local central limit theorem for the random walks on the discretized graphs, and identifies the limit through a martingale problem with duality. Without vertex selection the condition reduces to Kirchhoff's law, and without selection the limit is a Wright–Fisher SPDE on the graph.

## Sources

- Wai-Tong Louis Fan, "Stochastic PDEs on graphs as scaling limits of discrete interacting systems", *Bernoulli* 27(3) (2021), 1899–1941. <https://doi.org/10.3150/20-BEJ1296>
- Preprint version (the locators in this item follow its numbering): Wai-Tong Louis Fan, *Stochastic PDEs on graphs as scaling limits of discrete interacting systems*, arXiv:1708.01793, Theorem 1 (Section 4) and Theorems 3 and 4 (Section 5). <https://doi.org/10.48550/arXiv.1708.01793>
