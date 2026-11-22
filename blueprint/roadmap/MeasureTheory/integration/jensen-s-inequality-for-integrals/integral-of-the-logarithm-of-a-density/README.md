# Upper bound for the integral of the logarithm of a probability density over a set

Let $\mu$ be a measure and $f$ a $\mu$-integrable real function with $f > 0$ everywhere and
$\int f \, d\mu = 1$. For every measurable set $E$ with $0 < \mu(E) < \infty$ on which $\log f$ is
integrable,

$$\int_E \log f \, d\mu \le \mu(E) \log \frac{1}{\mu(E)}.$$

## Idea

Jensen's inequality says that $\varphi\left(\int g \, d\nu\right) \le \int \varphi(g)\, d\nu$ for a
convex function $\varphi$ and a probability measure $\nu$, with the inequality reversed for concave
$\varphi$. Apply it to the concave logarithm with $\nu$ the normalised restriction $\mu|_E / \mu(E)$:
the average of $\log f$ over $E$ is at most the logarithm of the average of $f$ over $E$, which is
at most $\log(1/\mu(E))$ because $\int_E f \le 1$.

## Statements

- [Upper bound for the integral of the logarithm of a probability density over a set](set-integral-log-le-measure-mul-log-inv.md)
