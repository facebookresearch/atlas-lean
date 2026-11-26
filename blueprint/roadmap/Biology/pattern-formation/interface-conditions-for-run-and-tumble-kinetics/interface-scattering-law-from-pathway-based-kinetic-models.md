# Interface scattering law for run-and-tumble kinetics from pathway-based models

**Pathway-based kinetic model (PBKM).** Let $p(t,x,v,m)$ be the density of cells at position $x$ moving with velocity $v \in V$, where $V$ is bounded, and carrying an internal (methylation) state $m\in[M_l,M_r]$:

$$\partial_t p + v\cdot\nabla_x p + \partial_m\big(f(m - m_c(x))\,p\big) = \Lambda(m - m_c(x))\Big(\frac{1}{|V|}\int_V p\,dv' - p\Big),$$

with $p = 0$ at $m = M_l$ and $m = M_r$. The adaptation rate $f$ satisfies $f(0) = 0$, $f(y) < 0$ for $y > 0$ and $f(y) > 0$ for $y < 0$, so $m$ relaxes to the signal-dependent equilibrium $m_c(x)$. The tumbling rate $\Lambda$ increases with the deviation $m - m_c$. Its marginal $\bar p = \int p\,dm$ is usually modelled by a run-and-tumble kinetic model (RTKM) with a signal-dependent tumbling operator. That reduction is valid only for slowly varying signals.

**Sharp interface.** Take $x\in\mathbb{R}$, $v\in(-1,1)$, and a dark–light interface at $x = 0$ with $m_c = M_l$ on $\Omega_l = (-\infty,0)$ and $m_c = M_r$ on $\Omega_r = (0,\infty)$. Discretize $m$ into $n+1$ states $p_0,\dots,p_n$ by finite volumes with upwind adaptation fluxes. Then rescale with a small parameter $\epsilon$ so that adaptation, and tumbling in non-equilibrium states, are fast, and let $\epsilon\to0$.

**Result (formal limit).** As $\epsilon\to0$, the total density $\sum_i p_i^\epsilon$ converges to $P(t,x,v)$, which solves an RTKM in each region,

$$\partial_tP + v\partial_xP = \Lambda_0^l\Big(\tfrac12\int_{-1}^1P\,dv' - P\Big)\ \text{in }\Omega_l,\qquad \partial_tP + v\partial_xP = \Lambda_n^r\Big(\tfrac12\int_{-1}^1P\,dv' - P\Big)\ \text{in }\Omega_r,$$

with the tumbling rates of the adapted states on each side. The two sides are coupled by a nonlocal interface condition

$$v\,P(t,0^-,-v) = \mathscr{A}\big[\tau_-P(t,0^+,\cdot)\big],\qquad (\tau_-f)(v) = f(-v),$$

where $\mathscr{A}$ is an integral operator in velocity space. It is determined by a half-space (interface-layer) problem for the non-adapted states and depends on their tumbling and adaptation rates. $P$ generally jumps across the interface even when $\Lambda_0^l = \Lambda_n^r$, and the outgoing distribution at one velocity depends on the whole incoming velocity distribution. For the two-velocity model $v \in \{\pm1\}$, $\mathscr{A}$ reduces to an explicit transmission matrix, computed by solving a linear ODE system of size $2n+2$.

## Expansion

In the interior of $\Omega_l$, weighted $L^1$ estimates, with weight $w(x) = x^2e^x$ and cutoffs, show inductively that the non-adapted states $p_1,\dots,p_n$ vanish as $\epsilon\to0$. This is because both the adaptation and tumbling terms are dissipative on the fast scale, leaving only the equilibrium state $p_0$. Symmetrically, only $p_n$ survives in $\Omega_r$. Near $x = 0$, cells crossing the interface are out of equilibrium. Within a layer of width $O(\epsilon)$ they adapt and tumble, and some reverse direction. Solving the stretched-variable boundary-layer problem and keeping only its bounded solutions yields $\mathscr{A}$. The resulting law is asymmetric: cells entering the favourable region largely keep their direction, while those entering the unfavourable region are scattered back. This matches phototactic observations at dark–light boundaries. Numerical simulations with *E. coli*-like parameters show the interface relation becoming time-independent before the population reaches steady state. The derivation is formal, not a rigorous limit theorem.

## Sources

- S. Lei, J. Liang, W. Sun and M. Tang, "The interface scattering law for run-and-tumble kinetic models", arXiv:2611.07409 (2026), sections "The discrete model" and "Asymptotic Analysis" (statement of the limiting system, formal derivation and the three-species two-velocity example), <https://doi.org/10.48550/arXiv.2611.07409>.
