# Wave instability needs at least three components

Consider the $n$-component reaction–diffusion system $\partial_t u = D \nabla^2 u + f(u)$ with diagonal diffusion matrix $D = \operatorname{diag}(D_1, \dots, D_n)$, $D_i \ge 0$, and a homogeneous equilibrium $P$, $f(P) = 0$, that is stable without diffusion: every eigenvalue of $J = J_u f(P)$ has negative real part. A Fourier mode with $|k|^2 = \mu > 0$ evolves under $J - \mu D$. A **Turing instability** occurs when, as $\mu$ varies, a real eigenvalue of $J - \mu D$ crosses $0$, i.e. $\det(J - \mu D) = 0$ for some $\mu > 0$; a **wave instability** occurs when a pair of purely imaginary eigenvalues appears, i.e. $J - \mu D$ has eigenvalues $\pm i\omega$, $\omega \ne 0$, for some $\mu > 0$. For an increasing word $(i_1 < \dots < i_k)$, $M_{i_1 \dots i_k}$ is the principal minor of $J$ on rows and columns $i_1, \dots, i_k$.

**Proposition.** (i) If $n = 2$, no diagonal $D \ge 0$ gives a wave instability around $P$. (ii) If $n = 3$ and there are $1 \le i_1 < i_2 \le 3$ with $M_{i_1} + M_{i_2} > 0$ and $M_{i_1 i_2} > 0$, then there are diffusion rates $D_1, D_2, D_3 \ge 0$ for which the system develops a wave instability around $P$. Hence three is the minimal number of components for a wave instability.

## Depends on

- [Equal diffusion rates exclude diffusion-driven instability](equal-diffusion-excludes-diffusion-driven-instability.md)

## Expansion

For $n = 2$, $\operatorname{tr}(J - \mu D) = \operatorname{tr} J - \mu(D_1 + D_2) < 0$ for all $\mu > 0$, while a purely imaginary pair would need trace $0$. For $n = 3$, the conditions say that the $2 \times 2$ principal submatrix on $\{i_1, i_2\}$ has positive trace and positive determinant, so both its eigenvalues have positive real part. Setting the two corresponding diffusion rates to $0$ and the third positive leaves, for large $\mu$, that unstable oscillatory block; the paper shows through the coefficients of the purely imaginary eigenvalue condition $b_3\mu^3 + b_2\mu^2 + b_1\mu + b_0 = 0$ that a pair of eigenvalues crosses the imaginary axis at some $\mu^* > 0$. Conversely, if every $2 \times 2$ principal submatrix is stable, no wave instability occurs for $n = 3$.

## Sources

- E. Villar-Sepúlveda and A. R. Champneys, *General conditions for Turing and wave instabilities in reaction–diffusion systems*, J. Math. Biol. 86 (2023), 39. <https://doi.org/10.1007/s00285-023-01870-3> (PMCID: PMC9884266) Section 3, Lemmas 8–11 and Proposition 1.
