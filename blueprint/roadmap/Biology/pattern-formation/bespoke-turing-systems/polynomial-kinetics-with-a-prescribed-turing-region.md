# Polynomial kinetics with a prescribed Turing parameter region

Let $\Omega \subset \mathbb{R}^n$ be a parameter region bounded by a level set, $\Omega = \{p : S(p) > 0\}$. For $\alpha \ge 2$, the kinetics

$$f(u, v) = (\alpha - 2) + (1 - \alpha) u + u^\alpha v, \qquad g(u, v) = G + (F - G) v - F u v$$

have the steady state $(1, 1)$ with $f_u = f_v = 1$, $g_u = -F$ and $g_v = -G$ there. Taking $\alpha = 2$, $F = S(p) + 2$ and $G = 2$ gives the system

$$u_t = u_{xx} - u + u^2 v, \qquad v_t = D v_{xx} + 2 + S(p)\, v - \bigl(S(p) + 2\bigr) u v,$$

whose steady state $(1, 1)$ is Turing unstable for every $p \in \Omega$, provided the diffusion ratio and domain are large enough; it suffices that

$$D > \sup_{p \in \Omega} \Bigl(\sqrt{S(p)} + \sqrt{S(p) + 2}\Bigr)^2.$$

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Proof depends on

- [Nondimensional Turing conditions and the critical diffusion ratio](nondimensional-turing-conditions-and-critical-diffusion-ratio.md)

## Expansion

Requiring $f(1,1) = g(1,1) = 0$, $f_u = f_v = 1$, $g_u = -F$, $g_v = -G$ for $f = a_1 + b_1 u + c_1 u^\alpha v$ and $g = a_2 + b_2 v + c_2 uv$ forces $a_1 = \alpha - 2$, $b_1 = 1 - \alpha$, $c_1 = 1$, $a_2 = G$, $b_2 = F - G$, $c_2 = -F$, and $a_1 \ge 0$ (positivity near the origin) needs $\alpha \ge 2$. With $F' = S(p) + 1$ and $G' = 1$ the nondimensional condition $F' > G' > 0$ is exactly $S(p) > 0$, and $D_c = (\sqrt{F - G} + \sqrt{F})^2$ with $F - G = S(p)$. Where $S(p) < 0$ the determinant $F - G$ is negative, so the steady state is unstable to spatially constant modes and patterning there is not controlled.

## Sources

- T. E. Woolley, A. L. Krause and E. A. Gaffney, *Bespoke Turing systems*, Bull. Math. Biol. 83 (2021), 41. <https://doi.org/10.1007/s11538-021-00870-y> (PMCID: PMC7979634) Sections 2.1–2.2, Equations (22)–(29).
