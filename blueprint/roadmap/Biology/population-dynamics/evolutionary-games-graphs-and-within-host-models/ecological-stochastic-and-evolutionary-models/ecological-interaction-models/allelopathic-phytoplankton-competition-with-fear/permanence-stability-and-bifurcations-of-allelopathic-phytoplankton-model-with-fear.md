# Permanence, global stability and bifurcations of an allelopathic phytoplankton model with a fear effect

**Model.** A toxin-producing phytoplankton species $x$ competes with a non-toxic species $y$. The non-toxic species' growth is reduced by fear of the toxic one (factor $1/(1+kx)$) and by allelopathic toxin release (term $mxy$). In nondimensional form, with all parameters positive,

$$\frac{dx}{dt} = bx(1 - x - cy), \qquad \frac{dy}{dt} = y\Big(\frac{1}{1+kx} - y - ax - mxy\Big),$$

where $c$ and $a$ are interspecific competition coefficients, $k$ the fear level and $m$ the toxin release rate. Boundary equilibria are $E_0 = (0,0)$, $E_1 = (1,0)$ and $E_2 = (0,1)$. Let $k^* = 1/a - 1$ (so $y$ can invade $E_1$ iff $k < k^*$, i.e. $\frac{1}{1+k} > a$) and note $x$ can invade $E_2$ iff $c < 1$.

**Theorem.**

1. Solutions with positive initial data stay positive and bounded; the system is permanent if $0 < k < k^*$ and $0 < c < 1$.
2. $E_0$ is a source. $E_1$ is a hyperbolic stable node for $k > k^*$ and a saddle for $0 < k < k^*$; $E_2$ is a stable node for $c > 1$ and a saddle for $c < 1$; at $k = k^*$ (resp. $c = 1$) they are nonhyperbolic: saddle-nodes or nonhyperbolic saddles depending on $m$, except that at $c = 1$ and the critical value $m = m^{**}$ of the source $E_2$ is a degenerate stable node.
3. Depending on $m$ relative to thresholds $m_1 = 1 - ac - k$ and $m_2$, the system has zero, one or two positive equilibria; e.g. for $0 < c < 1$ and $0 < k < k^*$ there is a unique positive equilibrium $E_{2*}$, while for $c > 1$ and $m > m_2$ there can be two ($E_{1*}$ a saddle, $E_{2*}$ a stable node) that merge into a saddle-node $E_{3*}$.
4. There are no limit cycles in the open positive quadrant (Bendixson–Dulac with $B = 1/(xy)$), and the positive equilibrium $E_{2*}$ is globally asymptotically stable when $0 < c < 1$ and $0 < k < k^*$.
5. (Bifurcations.) A transcritical bifurcation occurs at $E_1$ as $k$ crosses $k^*$ and at $E_2$ as $c$ crosses $1$ (under nondegeneracy conditions on $m$); the toxin rate $m$ can turn the boundary transcritical bifurcation into a pitchfork, and, with the toxin rate $m$ as parameter, a saddle-node bifurcation of interior equilibria occurs at $E_{3*} = (E, (1-E)/c)$ at $m = m_{SN}$ when $m > m_1$, $0 < k < k^*$, $c > 1$ and $c \ne \dfrac{E^3k^3 + 3E^2k^2 + 3Ek + 1}{3E^2k^2 + 3Ek + 1}$. Here $E$ is the double root in $(0,1)$ of the cubic whose roots are the $x$-coordinates of positive equilibria, and $m_{SN} = \dfrac{-E^2k^2 + 2Eck - 2Ek + c - 1}{E^2(E^2k^2 + 2Ek + 1)}$ is the value of $m$ (together with $a = a_1$) at which that cubic and its derivative both vanish at $E$, as in Section 6 of the source.
6. (Space.) For the diffusive version on a bounded domain with Neumann conditions, solutions are global and classical; spatially homogeneous data reproduce the ODE dynamics, and with a spatially varying fear function $k(x)$ comparison with constant-fear systems gives attraction to boundary or interior states under parameter restrictions.

## Expansion

The invasion criteria at the single-species equilibria determine the boundary dynamics: fear lowers the intrinsic growth of the non-toxic species from $1$ to $1/(1+kx)$, so strong fear ($k > k^*$) alone lets the toxic species exclude it, whereas the toxin term $mxy$ vanishes at $E_1$ and only shapes interior equilibria and the direction of the bifurcations. The interior nullcline intersection reduces to a cubic-type equation in $x$ whose discriminant structure produces the saddle-node. The Dulac function $1/(xy)$ gives divergence $-b/y - (1+mx)/x < 0$, excluding periodic orbits, so permanence plus a unique locally stable interior equilibrium gives global stability.

## Sources

- Shangming Chen, Fengde Chen, Vaibhava Srivastava and Rana D. Parshad, "Dynamical Analysis of an Allelopathic Phytoplankton Model with Fear Effect", Qualitative Theory of Dynamical Systems 23 (2024), 189, <https://doi.org/10.1007/s12346-024-01047-3>; numbering as in arXiv:2309.08383: the nondimensional model and Theorems 1–7 (Sections 2–5), the transcritical, pitchfork and saddle-node bifurcation theorems (Section 6), and the reaction–diffusion results (Section 8).
