# Leaf covariances of the two-state symmetric process on a tree

Let $T$ be a phylogenetic tree with edge lengths and $\ell_{t_1 t_2}$ the path length between points $t_1, t_2$ of $T$. The two-state symmetric Markov process assigns $X(t) \in \{0, 1\}$ to each point, is stationary with $X(t) \sim \mathrm{Bern}(1/2)$, and has

$$\Pr\bigl(X(t_2) = X(t_1)\bigr) = \tfrac{1}{2}\bigl(1 + e^{-\ell_{t_1 t_2}}\bigr), \qquad \Pr\bigl(X(t_2) \ne X(t_1)\bigr) = \tfrac{1}{2}\bigl(1 - e^{-\ell_{t_1 t_2}}\bigr).$$

Then for leaves $u, v$ with values $X_u, X_v$,

$$\operatorname{Cov}(X_u, X_v) = \tfrac{1}{4} e^{-\ell_{uv}},$$

and the conditional law of $X(t_2)$ given $X(t_1) = \omega \in \{0, 1\}$ has variance $\tfrac{1}{4}\bigl(1 - e^{-2\ell_{t_1 t_2}}\bigr)$. On a forest the process is taken independent on each component, so leaves in different components are uncorrelated ($\ell_{uv} = \infty$).

## Depends on

- [Tree Space](../../not-yet-classified/phylogenetic-tree-space/tree-space.md)

## Expansion

$\operatorname{Cov}(X_u, X_v) = \Pr(X_u = X_v = 1) - \tfrac14 = \tfrac12 \cdot \tfrac12(1 + e^{-\ell_{uv}}) - \tfrac14$. Given $X(t_1) = \omega$, $X(t_2)$ is Bernoulli with success probability $\tfrac12(1 \pm e^{-\ell})$, whose variance is $\tfrac14(1 - e^{-2\ell})$. Equivalently, the parity of $X$ flips at the events of a rate-one Poisson process along each edge. The paper reparametrizes edges by $\lambda_e = 1 - e^{-\ell_e} \in [0, 1]$, so that infinite edges ($\lambda_e = 1$), i.e. disconnected forests, are included in wald space.

## Sources

- M. K. Garba et al., *Information geometry for phylogenetic trees*, J. Math. Biol. 82 (2021), 19. <https://doi.org/10.1007/s00285-021-01553-x> (PMCID: PMC7884381) Section 2.3, Equation (2.1) and Lemma 2.1; Section 2.4.
