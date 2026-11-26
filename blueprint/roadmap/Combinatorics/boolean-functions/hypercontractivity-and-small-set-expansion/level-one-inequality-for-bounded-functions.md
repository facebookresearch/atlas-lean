# Level-1 inequality for [−1, 1]-valued functions

For every $f : \{-1,1\}^n \to [-1, 1]$ with $\alpha = \mathbb{E}|f| \le 1/2$,

$$\mathbf{W}^1[f] \le 16\,\alpha^2\ln\frac{1}{\alpha}.$$

## Proof sketch

Let $\ell = f^{=1}$ be the degree-one part, so $\mathbf{W}^1[f] = \mathbb{E}[f\ell] \le \mathbb{E}[|f||\ell|]$. Split according to whether $|\ell| \le t$: the small part contributes at most $t\alpha$, and the large part is controlled by the subgaussian tail of the linear form $\ell$ (Hoeffding) since $|f| \le 1$; choosing $t \approx \|\ell\|_2\sqrt{\ln(1/\alpha)}$ gives the bound.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Level-1 Inequality](../structure-theorems-for-boolean-functions/level-one-inequality.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
