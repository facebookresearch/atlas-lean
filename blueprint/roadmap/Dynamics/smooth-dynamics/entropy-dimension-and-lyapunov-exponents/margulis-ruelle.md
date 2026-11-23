# Margulis–Ruelle inequality (planar case)

Let $T$ be a $C^2$ diffeomorphism of the
Euclidean plane $\mathbb{R}^2$, that is, a $C^2$ map with a $C^2$ two-sided inverse. Let
$K \subseteq \mathbb{R}^2$ be a compact set with $T(K) = K$, and let $\mu$ be an ergodic
$T$-invariant Borel probability measure on $\mathbb{R}^2$ with
$\mu(\mathbb{R}^2 \setminus K) = 0$. Write $h_\mu(T)$ for the Kolmogorov–Sinai entropy of $T$
with respect to $\mu$, and $\lambda_1(x)$ and $\lambda_2(x)$ for the upper and lower Lyapunov
exponents of $T$ at $x$. Then

$$h_\mu(T) \le \max(0, \int \lambda_1 \, d\mu) + \max(0, \int \lambda_2 \, d\mu).$$

## Sources

- David Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Brasil. Mat. 9 (1978), no. 1,
  83–87, DOI 10.1007/bf02584795.
- G. A. Margulis (1968, unpublished).
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §103 (Diffeomorphisms; the Margulis–Ruelle inequality is stated after the theorem),
  <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `margulis_ruelle` of the lean-eval benchmark.
