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

- D. Ruelle, *An inequality for the entropy of differentiable maps*, Bol. Soc. Brasil. Mat. 9 (1978); G. A. Margulis (1968, unpublished). Knill, *Some fundamental theorems in mathematics*, §103. Via leanprover/lean-eval@38361be, problem `margulis_ruelle`.
