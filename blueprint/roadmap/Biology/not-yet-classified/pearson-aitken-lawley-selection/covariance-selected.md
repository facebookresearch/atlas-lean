# Selected covariance blocks under linear regression selection

Let $\mu$ be a probability measure on $\Omega$, let $X : \Omega \to \mathbb{R}^p$ and $E : \Omega \to \mathbb{R}^q$ be measurable and independent under $\mu$, let every coordinate of $E$ be square-integrable under $\mu$, and let $Y = a + B X + E$ ([response](response.md)). Let the selection density $w : \mathbb{R}^p \to [0, \infty]$ be measurable with $\int^- w(X)\,d\mu = 1$, and let every coordinate of $X$ be square-integrable under the [selected measure](selected-measure.md) $\nu = w(X)\cdot\mu$. Then for all coordinates $i, j$,

$$\operatorname{Cov}_\nu(X_i, Y_j) = \sum_k \operatorname{Cov}_\nu(X_i, X_k) B_{jk}, \qquad \operatorname{Cov}_\nu(Y_i, Y_j) = \sum_{k,l} B_{ik} \operatorname{Cov}_\nu(X_k, X_l) B_{jl} + \operatorname{Cov}_\mu(E_i, E_j).$$

## Depends on

- [Selected Measure](selected-measure.md)
- [Response](response.md)

## Proof depends on

- [Selection on X preserves the residual](indep-fun-and-map-residual-selected.md)

## Sources

- A. C. Aitken, Note on selection from a multivariate normal population, Proc. Edinburgh Math. Soc. (2) 4 (1934), 106–110, p. 109, equation (7).
- D. N. Lawley, A note on Karl Pearson's selection formulae, Proc. R. Soc. Edinburgh A 62 (1943), 28–30.
