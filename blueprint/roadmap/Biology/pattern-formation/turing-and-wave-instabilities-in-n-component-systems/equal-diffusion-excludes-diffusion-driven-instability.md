# Equal diffusion rates exclude diffusion-driven instability

Consider the $n$-component reaction–diffusion system $\partial_t u = D \nabla^2 u + f(u)$ with diagonal diffusion matrix $D = \operatorname{diag}(D_1, \dots, D_n)$, $D_i \ge 0$, and a homogeneous equilibrium $P$, $f(P) = 0$, that is stable without diffusion: every eigenvalue of $J = J_u f(P)$ has negative real part. A Fourier mode with $|k|^2 = \mu > 0$ evolves under $J - \mu D$. Three situations are distinguished. A **neutral mode** is a $\mu > 0$ at which $J - \mu D$ has an eigenvalue on the imaginary axis: a **Turing (neutral) mode** when that eigenvalue is $0$, i.e. $\det(J - \mu D) = 0$, and a **wave (neutral) mode** when $J - \mu D$ has eigenvalues $\pm i\omega$, $\omega \ne 0$. A **crossing** is a neutral mode at which, as $\mu$ (or a parameter) varies through it, the eigenvalue passes from the open left into the open right half-plane; touching zero is not enough: for $J = \begin{pmatrix} 1 & 1 \\ -4 & -3 \end{pmatrix}$ and $D = \operatorname{diag}(1, 9)$, $\det(J - \mu D) = (1 - 3\mu)^2$ vanishes at $\mu = 1/3$ while the trace stays negative, so no eigenvalue ever becomes positive. A **growing mode** is a $\mu > 0$ at which $J - \mu D$ has an eigenvalue with positive real part; it is a **Turing instability** if that eigenvalue is real and a **wave instability** if it is nonreal. For an increasing word $(i_1 < \dots < i_k)$, $M_{i_1 \dots i_k}$ is the principal minor of $J$ on rows and columns $i_1, \dots, i_k$.

**Theorem.** If $D_1 = \dots = D_n = \delta \ge 0$, then for every $\mu > 0$ every eigenvalue of $J - \mu D$ has negative real part. Hence there is no neutral mode (Turing or wave), no crossing and no growing mode (neither a Turing nor a wave instability) around $P$.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

With $D = \delta I$, $\lambda$ is an eigenvalue of $J - \mu D$ exactly when $\lambda + \mu\delta$ is an eigenvalue of $J$. Stability of $J$ gives $\operatorname{Re}(\lambda) < -\mu\delta \le 0$, so no eigenvalue of $J - \mu D$ reaches the closed right half-plane for any $\mu > 0$. Unequal diffusion is therefore necessary for either instability.

## Sources

- E. Villar-Sepúlveda and A. R. Champneys, *General conditions for Turing and wave instabilities in reaction–diffusion systems*, J. Math. Biol. 86 (2023), 39. <https://doi.org/10.1007/s00285-023-01870-3> (PMCID: PMC9884266) Section 4, Theorem 3.
