# Young's entropy–dimension–Lyapunov formula (planar case)

Let $T$ be a $C^2$
diffeomorphism of the Euclidean plane $\mathbb{R}^2$: $T$ has a two-sided inverse $T^{-1}$ and
both $T$ and $T^{-1}$ are $C^2$. Let $K \subseteq \mathbb{R}^2$ be a compact set with
$T(K) = K$, and let $\mu$ be a Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$ that is $T$-invariant and ergodic for $T$. Let $\lambda_1$
and $\lambda_2$ be the $\mu$-integrals of the upper and the lower Lyapunov exponent of $T$. Then
the Kolmogorov–Sinai entropy of $T$ with respect to $\mu$ is

$$h_\mu(T) = \frac{\dim(\mu) \cdot H}{2},$$

where $\dim(\mu)$ is the Hausdorff dimension of $\mu$ and
$H = \frac{2 \lambda_1 (-\lambda_2)}{\lambda_1 - \lambda_2}$ is the harmonic mean of $\lambda_1$
and $-\lambda_2$, taken to be $0$ when $\lambda_1 = \lambda_2$.

## Sources

- Lai-Sang Young, *Dimension, entropy and Lyapunov exponents*, Ergodic Theory Dynam. Systems 2 (1982), no. 1,
  109–124, DOI 10.1017/s0143385700009615.
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §103 (Diffeomorphisms; the theorem of the section),
  <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `entropy_dimension_lyapunov` of the lean-eval benchmark.
