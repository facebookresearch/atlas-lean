# Unstable principal subsystems enable diffusion-driven instability

Let $n \ge 2$ and let $A = (a_{ij}) \in \mathbb{R}^{n \times n}$ be the Jacobian of the kinetics $u_t = f(u)$ at a spatially uniform steady state $u_s$ of the reaction-diffusion system

$$\partial_t u_j = D_j \,\partial_x^2 u_j + f_j(u), \qquad j = 1, \dots, n,$$

with diffusion coefficients $D_1, \dots, D_n \ge 0$. A Fourier mode of wavenumber $k \in \mathbb{R}$ evolves under the matrix $C(k) = A - k^2 D$, $D = \operatorname{diag}(D_1, \dots, D_n)$. Assume $A$ is stable (every eigenvalue has negative real part). For a nonempty proper index set $J \subsetneq \{1, \dots, n\}$, write $A_J$ for the principal submatrix of $A$ on the rows and columns in $J$; the linear system $\dot v = A_J v$ is the **subsystem** on the species in $J$.

**Theorem (unstable subsystem implies Turing instability).** If some principal submatrix $A_J$ has an eigenvalue with positive real part, then there are diffusion coefficients $D_1, \dots, D_n > 0$ and a wavenumber $k \neq 0$ such that $C(k)$ has an eigenvalue with positive real part, i.e. the uniform state is stable for the kinetics but unstable for the reaction-diffusion system. One can take $D_j$ small for $j \in J$ and $D_j$ large for $j \notin J$.

Conversely, if every principal minor of $A$ satisfies $\operatorname{sgn} \det A_J = (-1)^{|J|}$ (all subsystems sign-stable), no choice of $D \ge 0$ produces a steady Turing bifurcation. Satnoianu, Menzinger and Maini call a Turing bifurcation **of type $p$** when the smallest unstable subsystem has $p$ species, $1 \le p \le n - 1$: type I means some $a_{ii} > 0$ (a single self-activating species, the classical activator), type II means no $a_{ii} > 0$ but some $2 \times 2$ principal minor $\det A_{\{i,j\}} < 0$, and so on. For $n = 2$ only type I exists; for $n \ge 3$ the "activator" can be a network of several species none of which is self-activating.

## Depends on

- [Diffusion-driven instability (Turing 1952)](turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Order the species so that $J = \{1, \dots, p\}$ and write $A = \begin{pmatrix} A_J & B \\ E & A_K \end{pmatrix}$. Fix $k \ne 0$, set $D_j = 0$ for $j \in J$ and $D_j = L$ for $j \notin J$. For $\lambda$ in a fixed bounded set and $L$ large, $A_K - k^2 L I - \lambda I$ is invertible with inverse of norm $O(1/L)$, so by the Schur complement the eigenvalues of $C(k)$ in that set are the roots of $\det\big(A_J - \lambda I - B(A_K - k^2 L I - \lambda I)^{-1} E\big)$, which converge to the eigenvalues of $A_J$ as $L \to \infty$; the remaining $n - p$ eigenvalues tend to $-\infty$. Hence for $L$ large $C(k)$ inherits an eigenvalue of positive real part from $A_J$, and by continuity of eigenvalues the same holds after replacing the zero coefficients on $J$ by small positive ones. Because $A$ itself is stable, the $k = 0$ mode is stable, so the instability is diffusion driven. The original argument tracks instead the constant term $c_n = \det(-C(k))$ of the characteristic polynomial, which is multilinear in the $D_j$, and tunes one coefficient until $c_n$ changes sign, producing a zero eigenvalue (a steady Turing bifurcation). The principal-minor characterization of matrices that stay stable for every nonnegative diagonal diffusion ("strong stability") goes back to Cross (1978).

## Sources

- R. A. Satnoianu, M. Menzinger and P. K. Maini, "Turing instabilities in general systems", Journal of Mathematical Biology 41 (2000), 493–512, Section 2 (Theorems 1–3, Eq. (2.23), Remark 5 and the definition of type-$p$ bifurcations), <https://doi.org/10.1007/s002850000056>.
