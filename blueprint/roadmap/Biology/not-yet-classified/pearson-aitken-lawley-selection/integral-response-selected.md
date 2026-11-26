# Selected means under linear regression selection

Let $\mu$ be a probability measure on $\Omega$, let $X : \Omega \to \mathbb{R}^p$ and $E : \Omega \to \mathbb{R}^q$ be measurable and independent under $\mu$, let every coordinate of $E$ be $\mu$-integrable with mean $0$, and let $Y = a + B X + E$ ([response](response.md)). Let the selection density $w : \mathbb{R}^p \to [0, \infty]$ be measurable with $\int^- w(X)\,d\mu = 1$, and let every coordinate of $X$ be integrable under the [selected measure](selected-measure.md) $\nu = w(X)\cdot\mu$. Then for every coordinate $j$,

$$\int Y_j\,d\nu = a_j + \sum_k B_{jk} \int X_k\,d\nu.$$

## Depends on

- [Selected Measure](selected-measure.md)
- [Response](response.md)

## Proof depends on

- [Selection on X preserves the residual](indep-fun-and-map-residual-selected.md)

## Sources

- A. C. Aitken, Note on selection from a multivariate normal population, Proc. Edinburgh Math. Soc. (2) 4 (1934), 106–110, p. 109, equation (5).
