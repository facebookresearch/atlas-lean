# Sinclair's canonical-path bound on the spectral gap

Let $P$ be a real matrix on a finite state space $S$ with unit row sums, reversible with respect to a probability vector $\pi > 0$: $\pi(x) P(x,y) = \pi(y) P(y,x)$ for all $x, y$. Give every ordered pair of distinct states a path $\gamma_{xy}$ from $x$ to $y$, and let $B$ be a real number with

$$\sum_{x \ne y} \pi(x)\pi(y)\,|\gamma_{xy}|\, m_{xy}(u,v) \;\le\; B\, \pi(u) P(u,v) \quad\text{for every oriented edge } (u,v),$$

where $m_{xy}(u,v)$ counts the uses of $(u,v)$ by $\gamma_{xy}$. Then every real eigenvalue $\mu \ne 1$ of $P$ (with a nonzero real eigenvector $f$, $Pf = \mu f$) satisfies $1 \le B(1-\mu)$. When the paths use only transitions of positive probability, Sinclair's length-weighted congestion $\bar\rho(\Gamma)$ is such a $B$, so the spectral gap is at least $1/\bar\rho(\Gamma)$: this is Sinclair's Theorem 5, stated there as $\lambda_1 \le 1 - 1/\bar\rho$ for the second eigenvalue $\lambda_1$.

The proof follows the paper: an eigenvector $f$ for $\mu \ne 1$ has $\pi$-mean zero because $\pi$ is stationary, so its variance and Dirichlet form are $\sum_x \pi(x) f(x)^2$ and $(1-\mu)\sum_x \pi(x) f(x)^2$, and the canonical-path Poincaré inequality compares them. No eigenvalue need be ordered, and no spectral theorem is used; nonnegativity of $P$ is not needed either.

## Background

- [Detailed balance](../finite-continuous-time-markov-chains/stationarity-and-detailed-balance-for-finite-con/is-detailed-balance.md): the hypothesis $\pi(x) P(x,y) = \pi(y) P(y,x)$ used here, shared with the continuous-time chains and substitution models.
- [Detailed balance](../kolmogorov-s-criterion-for-reversibility/detailed-balance.md): the same equations for the stochastic matrices on $\{0, \dots, M\}$ of Kolmogorov's criterion.
- [Graph Laplacians and Cheeger's inequality](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md): the Dirichlet form $\tfrac12\sum_{x,y} \pi(x)P(x,y)(f(x)-f(y))^2$ is the Laplacian quadratic form of the graph with edge weights $\pi(x)P(x,y)$.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Theorem 5.
