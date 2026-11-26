# Equal diffusion rates exclude diffusion-driven instability

Consider the $n$-component reaction–diffusion system $\partial_t u = D \nabla^2 u + f(u)$ with diagonal diffusion matrix $D = \operatorname{diag}(D_1, \dots, D_n)$, $D_i \ge 0$, and a homogeneous equilibrium $P$, $f(P) = 0$, that is stable without diffusion: every eigenvalue of $J = J_u f(P)$ has negative real part. A Fourier mode with $|k|^2 = \mu > 0$ evolves under $J - \mu D$. A **Turing instability** occurs when, as $\mu$ varies, a real eigenvalue of $J - \mu D$ crosses $0$, i.e. $\det(J - \mu D) = 0$ for some $\mu > 0$; a **wave instability** occurs when a pair of purely imaginary eigenvalues appears, i.e. $J - \mu D$ has eigenvalues $\pm i\omega$, $\omega \ne 0$, for some $\mu > 0$. For an increasing word $(i_1 < \dots < i_k)$, $M_{i_1 \dots i_k}$ is the principal minor of $J$ on rows and columns $i_1, \dots, i_k$.

**Theorem.** If $D_1 = \dots = D_n = \delta \ge 0$, the system admits neither a Turing nor a wave instability around $P$.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

With $D = \delta I$, $\lambda$ is an eigenvalue of $J - \mu D$ exactly when $\lambda + \mu\delta$ is an eigenvalue of $J$. Stability of $J$ gives $\operatorname{Re}(\lambda) < -\mu\delta \le 0$, so no eigenvalue of $J - \mu D$ reaches the imaginary axis for any $\mu > 0$. Unequal diffusion is therefore necessary for either instability.

## Sources

- E. Villar-Sepúlveda and A. R. Champneys, *General conditions for Turing and wave instabilities in reaction–diffusion systems*, J. Math. Biol. 86 (2023), 39. <https://doi.org/10.1007/s00285-023-01870-3> (PMCID: PMC9884266) Section 4, Theorem 3.
