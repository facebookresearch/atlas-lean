# Fickian release from a sphere into a perfect sink

A dissolved drug initially uniform in a sphere of radius $R$, released by constant-coefficient diffusion into a perfect sink, leaves with fraction $1 - \tfrac{6}{\pi^2}\sum_{n\ge1} n^{-2}e^{-Dn^2\pi^2t/R^2}$.

Let $R > 0$, $D > 0$ and $c_i > 0$. Let $c(r,t)$ be the bounded radially symmetric solution of $c_t = D\,r^{-2}(r^2 c_r)_r$ in the ball $0 \le r < R$ (regular at the centre, $c_r(0,t) = 0$, equivalently $u = rc$ satisfies $u(0,t) = 0$), with $c(r,0) = c_i$ for $0 \le r < R$ and $c(R,t) = 0$ for $t > 0$. Then the cumulative fraction released is

$$\frac{M_t}{M_\infty} = 1 - \frac{6}{\pi^2}\sum_{n=1}^{\infty}\frac{1}{n^2}\exp\left(-\frac{D n^2\pi^2 t}{R^2}\right),$$

with $M_\infty = \tfrac43\pi R^3 c_i$.

## Context

Undergraduate. The source obtains it as the $a = 0$, $b = R$ case of release from a spherical shell (its Eq. (21)) and applies it to PLGA microspheres whose volume did not change appreciably during that experiment, treating them as non-degrading for that purpose. For small $t$, $M_t/M_\infty = 6\sqrt{Dt/\pi}/R - 3Dt/R^2$ plus exponentially small terms, so the curve starts as $\sqrt t$ but is not a single power law.

## Depends on

None.

## Proof depends on

- [Single-mode solution of the Dirichlet heat equation](../../../../Analysis/partial-differential-equations/heat-equation/single-mode-solution-of-the-dirichlet-heat-equation.md)

## Expansion

With $u = rc$ the problem becomes $u_t = Du_{rr}$ on $(0,R)$ with $u(0,t) = u(R,t) = 0$; expand $u(r,0) = c_i r$ in $\sin(n\pi r/R)$, integrate $4\pi r^2 c$ over the ball, and use $\sum n^{-2} = \pi^2/6$. Uniqueness among bounded radial solutions (regularity at $r = 0$) and the short-time expansion need their own lemmas.

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 2.6.1 Eq. (21) and Section 2.6.2 Eq. (22) with the surrounding discussion of non-degrading polymer microspheres
