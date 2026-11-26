# Talagrand's concentration inequality around the mean

There are absolute constants $C, c > 0$ with the following property. Let $K > 0$, let
$X_1, \dots, X_n$ be independent real random variables with $|X_i| \le K$, and let
$F : \mathbb{R}^n \to \mathbb{R}$ be convex and $1$-Lipschitz for the Euclidean metric. Then, with
$X = (X_1, \dots, X_n)$,

$$\mathbb{P}\big(|F(X) - \mathbb{E} F(X)| \ge \lambda K\big) \le C e^{-c\lambda^2} \quad
\text{for every } \lambda > 0.$$

$F(X)$ is bounded and measurable, so its expectation exists. This is the real case of Tao's
complex statement.

## Informally uses

- [Talagrand's concentration inequality around a median](talagrand-concentration-median.md):
  integrating the median tail bound shows that the mean and a median differ by $O(K)$.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, Theorem 2.1.13, inequality (2.19).
