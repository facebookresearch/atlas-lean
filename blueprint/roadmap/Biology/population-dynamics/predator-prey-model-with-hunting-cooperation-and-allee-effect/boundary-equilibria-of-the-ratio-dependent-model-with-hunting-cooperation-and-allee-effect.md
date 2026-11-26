# Boundary equilibria of the ratio-dependent predator–prey model with hunting cooperation and an Allee effect

**Setting.** Let $u\ge0$ be the (scaled) prey and $v\ge0$ the predator density. The prey grows with a cubic Allee law with threshold $b\in(-1,1)$ (strong Allee effect for $b>0$, weak for $b<0$) and is consumed through a ratio-dependent functional response in which cooperative hunting with strength $\alpha\ge0$ raises the effective attack rate by the factor $1+\alpha v$:

$$\frac{du}{dt}=a\,u(u-b)(1-u)-\frac{uv(1+\alpha v)}{v+(1+\alpha v)u},\qquad \frac{dv}{dt}=\frac{c\,uv(1+\alpha v)}{v+(1+\alpha v)u}-d\,v,$$

with growth rate $a>0$, conversion efficiency $c>0$ and predator death rate $d>0$.

**Theorem.**
1. (Equilibria) The system always has the boundary equilibria $(0,0)$, $(1,0)$ and $(b,0)$ (the last in the first quadrant when $b>0$), and, depending on the parameters, none, one or two interior equilibria.
2. (Stability of the carrying capacity) The predator-free state $(1,0)$ has Jacobian eigenvalues $-a(1-b)$ and $c-d$; it is locally asymptotically stable when $c<d$ and a saddle when $c>d$.
3. (Allee threshold) For $b>0$ the predator-free state $(b,0)$ is unstable: its prey eigenvalue is $a\,b(1-b)>0$.

So predators cannot invade the prey at carrying capacity unless their maximal conversion rate $c$ exceeds their death rate $d$, independently of the cooperation strength $\alpha$; cooperation affects only the interior equilibria.

## Expansion

At $v=0$ the predation term and its $u$-derivative vanish, while its $v$-derivative at $(u,0)$ equals $1$ (the ratio-dependent response saturates at one prey per predator), so the Jacobian at $(u^*,0)$ is upper triangular with diagonal $\big(a\,\tfrac{d}{du}[u(u-b)(1-u)]_{u^*},\ c-d\big)$, which gives parts 2–3. Interior equilibria satisfy $c\,u(1+\alpha v)=d\,(v+(1+\alpha v)u)$, i.e. $v=\frac{(c-d)u}{d-\alpha(c-d)u}$, which needs $c>d$ and $u<\frac{d}{\alpha(c-d)}$; substituting into the prey equation gives $a(u-b)(1-u)\big(d-\alpha(c-d)u\big)=\frac{d(c-d)}{c}$, a polynomial equation whose admissible roots are the coexistence states. The origin is a singular point of the ratio-dependent vector field and needs a separate blow-up analysis.

## Sources

- Aaditya Kharel, Zhifu Xie, Huiqing Zhu, Michelle McCullum, "Predator-Prey Interaction Model with Hunting Cooperation among Predators and Allee Effect in Prey", arXiv:1911.10299 (2019), model (1.1), Theorem 1.1 and Theorem 2.1, <https://doi.org/10.48550/arXiv.1911.10299>.
