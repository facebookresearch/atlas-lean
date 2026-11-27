# Nondimensional Turing conditions and the critical diffusion ratio

Linearize a two-species system $u_t = D_u u_{xx} + f(u, v)$, $v_t = D_v v_{xx} + g(u, v)$ at a homogeneous steady state with Jacobian sign structure $f_u, f_v > 0$ and $g_u, g_v < 0$. Rescaling time by $1/f_u$, space by $\sqrt{D_u / f_u}$ and the perturbations so that $f_u [u] = f_v [v]$ gives

$$u_t = u_{xx} + u + v, \qquad v_t = D v_{xx} - F u - G v,$$

with $F = |g_u| f_v / f_u^2$, $G = |g_v| / f_u$ and $D = D_v / D_u$, all positive. A Fourier mode $e^{ikx}$, $k \in \mathbb R$, evolves under $J - k^2\operatorname{diag}(1, D)$ with $J = \begin{pmatrix} 1 & 1 \\ -F & -G \end{pmatrix}$. **Continuous wavenumbers.** The steady state is stable without diffusion ($J$ has both eigenvalues in the open left half-plane) and some real wavenumber $k$ has a mode with a positive eigenvalue if and only if

$$F > G > 1 \qquad \text{and} \qquad D - G > 2\sqrt{D (F - G)}.$$

The unstable wavenumbers then form the band $k_-^2 < k^2 < k_+^2$, where $k_\pm^2 = \bigl(D - G \pm \sqrt{(D - G)^2 - 4D(F - G)}\bigr)/(2D)$ are the roots of $h(k^2) = \det\bigl(J - k^2\operatorname{diag}(1, D)\bigr) = Dk^4 - (D - G)k^2 + (F - G)$.

**Finite domain.** On a bounded interval $[0, L]$ (length in the rescaled space variable) with Neumann boundary conditions only the wavenumbers $k = n\pi/L$, $n = 1, 2, \dots$, are available, and the band can contain none of them when $L$ is small. The steady state is stable without diffusion and diffusion-driven unstable on $[0, L]$ if and only if $F > G > 1$, $D - G > 2\sqrt{D(F - G)}$, and $k_-^2 < (n\pi/L)^2 < k_+^2$ for some integer $n \ge 1$.

Given $F > G > 1$, the condition $D - G > 2\sqrt{D (F - G)}$ holds exactly when

$$D > D_c = \bigl(\sqrt{F - G} + \sqrt{F}\bigr)^2.$$

Writing $F' = F - 1$ and $G' = G - 1$, the only kinetic requirement is $F' > G' > 0$; any $D > D_c$ gives a nonempty band, and a long enough domain then contains an unstable mode.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

The rescaled Jacobian is $\begin{pmatrix} 1 & 1 \\ -F & -G \end{pmatrix}$. Stability without diffusion needs trace $1 - G < 0$ and determinant $F - G > 0$. Since $\operatorname{tr}(J - k^2\operatorname{diag}(1,D)) = 1 - G - (1 + D)k^2 < 0$, a mode is unstable exactly when $h(k^2) < 0$, and $h$ takes a negative value at some $k^2 > 0$ iff its vertex $k^2 = (D - G)/(2D)$ is positive and its discriminant is positive. The classical diffusion condition $D_v f_u + D_u g_v > 2\sqrt{D_u D_v (f_u g_v - f_v g_u)}$ becomes $D - G > 2\sqrt{D(F - G)}$, equivalently $(\sqrt{D} - \sqrt{F - G})^2 > F$ with $\sqrt{D} > \sqrt{F-G}$, which is $\sqrt{D} > \sqrt{F - G} + \sqrt{F}$. In words, inhibition of the inhibitor by the activator must exceed self-inhibition, which must exceed self-activation.

## Sources

- T. E. Woolley, A. L. Krause and E. A. Gaffney, *Bespoke Turing systems*, Bull. Math. Biol. 83 (2021), 41. <https://doi.org/10.1007/s11538-021-00870-y> (PMCID: PMC7979634) Section 2.1, Equations (4)–(19).
