# Tonelli's theorem for iterated integrals

Let $\mu$ and $\nu$ be s-finite measures on sets $\alpha$ and $\beta$ with σ-algebras, for instance σ-finite measures.
If $f \colon \alpha \times \beta \to [0, \infty]$ is almost everywhere measurable for the product measure
$\mu \times \nu$, that is, equal almost everywhere to a measurable function, then

$$\int \Big( \int f(x, y) \, d\nu(y) \Big) \, d\mu(x) = \int \Big( \int f(x, y) \, d\mu(x) \Big) \, d\nu(y)$$

in $[0, \infty]$. Here the integral of a function $h$ with values in $[0, \infty]$, measurable or not, is the supremum
of $\sum_j c_j \mu(A_j)$ over the simple functions $\sum_j c_j \chi_{A_j} \le h$ with $A_j$ disjoint measurable sets and
$c_j \in [0, \infty]$, so the inner integrals are defined at every point.
