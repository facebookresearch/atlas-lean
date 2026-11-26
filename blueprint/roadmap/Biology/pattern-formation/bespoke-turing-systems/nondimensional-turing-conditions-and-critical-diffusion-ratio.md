# Nondimensional Turing conditions and the critical diffusion ratio

Linearize a two-species system $u_t = D_u u_{xx} + f(u, v)$, $v_t = D_v v_{xx} + g(u, v)$ at a homogeneous steady state with Jacobian sign structure $f_u, f_v > 0$ and $g_u, g_v < 0$. Rescaling time by $1/f_u$, space by $\sqrt{D_u / f_u}$ and the perturbations so that $f_u [u] = f_v [v]$ gives

$$u_t = u_{xx} + u + v, \qquad v_t = D v_{xx} - F u - G v,$$

with $F = |g_u| f_v / f_u^2$, $G = |g_v| / f_u$ and $D = D_v / D_u$, all positive. The steady state is stable without diffusion and driven unstable by diffusion if and only if

$$F > G > 1 \qquad \text{and} \qquad D - G > 2\sqrt{D (F - G)}.$$

Given $F > G > 1$, the second condition holds exactly when

$$D > D_c = \bigl(\sqrt{F - G} + \sqrt{F}\bigr)^2.$$

Writing $F' = F - 1$ and $G' = G - 1$, the only kinetic requirement is $F' > G' > 0$; a large enough $D$ and domain then always give an unstable mode.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

The rescaled Jacobian is $\begin{pmatrix} 1 & 1 \\ -F & -G \end{pmatrix}$. Stability without diffusion needs trace $1 - G < 0$ and determinant $F - G > 0$. The classical diffusion condition $D_v f_u + D_u g_v > 2\sqrt{D_u D_v (f_u g_v - f_v g_u)}$ becomes $D - G > 2\sqrt{D(F - G)}$, equivalently $(\sqrt{D} - \sqrt{F - G})^2 > F$ with $\sqrt{D} > \sqrt{F-G}$, which is $\sqrt{D} > \sqrt{F - G} + \sqrt{F}$. In words, inhibition of the inhibitor by the activator must exceed self-inhibition, which must exceed self-activation.

## Sources

- T. E. Woolley, A. L. Krause and E. A. Gaffney, *Bespoke Turing systems*, Bull. Math. Biol. 83 (2021), 41. <https://doi.org/10.1007/s11538-021-00870-y> (PMCID: PMC7979634) Section 2.1, Equations (4)–(19).
