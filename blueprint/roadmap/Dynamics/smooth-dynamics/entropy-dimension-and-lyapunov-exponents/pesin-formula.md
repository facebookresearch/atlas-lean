# Pesin entropy formula (planar case)

Let $T$ be a $C^2$ diffeomorphism of the Euclidean
plane $\mathbb{R}^2$, that is, a $C^2$ map with a $C^2$ two-sided inverse. Let
$K \subseteq \mathbb{R}^2$ be a compact set with $T(K) = K$, and let $\mu$ be an ergodic
$T$-invariant Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$. Write $h_\mu(T)$ for the Kolmogorov–Sinai entropy of $T$
with respect to $\mu$, and $\lambda_1(x)$ and $\lambda_2(x)$ for the upper and lower Lyapunov
exponents of $T$ at $x$. Suppose that the Hausdorff dimension of $\mu$ equals $2$ and that
$\int \lambda_1 \, d\mu = -\int \lambda_2 \, d\mu$. Then $h_\mu(T) = \int \lambda_1 \, d\mu$.

## Sources

- Ya. B. Pesin, *Characteristic Lyapunov exponents and smooth ergodic theory*, Russian Math. Surveys 32 (1977),
  no. 4, 55–114, DOI 10.1070/rm1977v032n04abeh001639.
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §103 (Diffeomorphisms; Pesin's formula as the case $\dim(\mu) = 2$, $\lambda_1 = -\lambda_2$),
  <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `pesin_formula` of the lean-eval benchmark.
