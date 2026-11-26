# Density-dependent reduced chemostat and bistability under flocculation

**Model.** In a chemostat with dilution rate $D$ and input substrate $S_{in}$, a species is present as isolated individuals $u$ (growth $f(S)$, removal $D_0$) and as flocs $v$ (growth $g(S)$, removal $D_1$). Isolated individuals aggregate at rate $a(u+v)u$ and flocs split at rate $bv$; with flocculation fast relative to growth (rates $a/\varepsilon$, $b/\varepsilon$),

$$\dot S = D(S_{in} - S) - f(S)u - g(S)v, \quad \dot u = (f(S) - D_0)u - \tfrac{a}{\varepsilon}(u+v)u + \tfrac{b}{\varepsilon}v, \quad \dot v = (g(S) - D_1)v + \tfrac{a}{\varepsilon}(u+v)u - \tfrac{b}{\varepsilon}v.$$

**Theorem (slow-fast reduction).** Let $x = u + v$ and $p(x) = b/(b+ax)$. For $S_0 \ge 0$, $u_0 > 0$, $v_0 \ge 0$, as $\varepsilon \to 0$ the solution satisfies $S = \overline{S} + o(1)$ and $x = \overline{x} + o(1)$ uniformly on $[0,T]$, and $u = p(\overline{x})\overline{x} + o(1)$, $v = (1-p(\overline{x}))\overline{x} + o(1)$ uniformly on $[t_0,T]$ for any $t_0 > 0$, where $(\overline{S},\overline{x})$ solves the reduced chemostat

$$\dot S = D(S_{in} - S) - \mu(S,x)x, \qquad \dot x = (\mu(S,x) - d(x))x, \qquad \mu(S,x) = \frac{bf(S) + axg(S)}{b+ax}, \quad d(x) = \frac{bD_0 + axD_1}{b+ax},$$

with $\overline S(0) = S_0$, $\overline x(0) = u_0 + v_0$. Both the growth function and the apparent removal rate are density dependent.

**Theorem (one-species reduced model).** Assume $\mu(0,x) = 0$, $\mu > 0$ for $S > 0$, $\partial_S\mu > 0 > \partial_x\mu$, and $d(0) = D_0 > d(+\infty) = D_1$, $d' < 0$, $(xd)' > 0$ (with $D_0 \le D$). Let $f(S) = \mu(S,0)$, $g(S) = \mu(S,+\infty)$, $\lambda_0 = f^{-1}(D_0)$, $\lambda_1 = g^{-1}(D_1)$ (or $+\infty$), plus the sign conditions H3/H4 comparing $d'(x)$ with $\partial_x\mu$ between $\lambda_0$ and $\lambda_1$.
1. The washout equilibrium $E_0 = (S_{in},0)$ is a saddle if $\lambda_0 < S_{in}$ and a stable node if $\lambda_0 > S_{in}$.
2. If $\lambda_0 < \min(\lambda_1, S_{in})$, there is a unique positive equilibrium, and it is locally asymptotically stable; if $S_{in} < \lambda_0 < \lambda_1$ there is none.
3. If $\lambda_1 < \lambda_0 < S_{in}$, there is an odd number (generically) of positive equilibria, alternately stable nodes and saddles; if $\lambda_1 < S_{in} < \lambda_0$, there are generically none or an even number, again alternating. In the latter case the stable washout coexists with stable positive equilibria: **bistability with monotone growth functions**, which the classical chemostat only shows for non-monotone growth.

## Expansion

The fast subsystem conserves $x = u+v$ and relaxes to the slow invariant curve $a(u+v)u = bv$, i.e. $u = p(x)x$; Tikhonov's theorem gives the approximation away from an initial layer. On this slow curve the population behaves as one species whose per-capita growth $\mu(S,x)$ and removal $d(x)$ interpolate between isolated and flocculated values according to the floc fraction $1 - p(x)$. Positive equilibria solve $\mu(S,x) = d(x)$ together with $D(S_{in} - S) = d(x)x$, and when flocs grow worse but are washed out less ($\lambda_1 < \lambda_0$) the curve can cross several times, producing alternating stability.

## Sources

- Radhouene Fekih-Salem, Jérôme Harmand, C. Lobry, Alain Rapaport and Tewfik Sari, "Extensions of the chemostat model with flocculation", arXiv:1106.6038 (2011), Section 3, Theorem 3.1, and Section 4, Propositions 4.2-4.5, <https://doi.org/10.48550/arXiv.1106.6038>.
