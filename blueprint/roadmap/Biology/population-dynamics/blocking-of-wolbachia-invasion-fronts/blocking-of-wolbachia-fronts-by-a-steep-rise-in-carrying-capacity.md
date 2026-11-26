# Blocking of Wolbachia invasion fronts by a steep rise in carrying capacity

Consider the one-dimensional reduced Wolbachia equation for the infection fraction $p(t,x) \in [0,1]$,

$$
\partial_t p - \partial_{xx} p - 2\frac{K'}{K}\,\partial_x p = f(p) + \frac{K''}{K}\, g(p), \qquad x \in \mathbb{R},
$$

with the bistable reaction $f$ and the heterogeneity term $g$ of the high-fecundity reduction (parameters $\delta > 1$, $0 < s_f < 1$, $0 < s_h \le 1$, $s_f + \delta - 1 < s_h\delta$), and suppose $F(1) = \int_0^1 f > 0$, so that in a homogeneous environment the unique bistable travelling wave invades ($p \to 1$). Let the carrying capacity rise exponentially over a region of length $L$:

$$
K(x) = A \ \ (x < 0), \qquad K(x) = A e^{Cx} \ \ (0 \le x \le L), \qquad K(x) = A e^{CL} \ \ (x > L).
$$

A **$(C, L)$-barrier** is a positive solution of the stationary problem $-p'' - 2Cp' - C^2 g(p) = f(p)$ on $(0, L)$, $-p'' = f(p)$ outside $[0, L]$, with jump conditions $p'(0^-) - p'(0^+) = C g(p(0))$, $p'(L^-) - p'(L^+) = -C g(p(L))$, and limits $p(-\infty) = 1$, $p(+\infty) = 0$.

**Theorem (existence of barriers).** There is $C^* > 0$, with $C^* \le 2\sqrt{2F(1)}/g_\infty$ where $g_\infty = \max_{(0, s_f/s_h)} g$, such that for every $C > C^*$ a $(C, L)$-barrier exists for some $L > 0$; the barrier can be taken decreasing. If a $(C_1, L_1)$-barrier exists, then for every $L_2 > L_1$ a $(C_2, L_2)$-barrier exists with $C_2 = C_1 L_1/L_2$: what matters is the total rise $CL$ of $\log K$, which can be spread over a longer region.

**Proposition (blocking).** If $\overline{P}$ is a $(C, L)$-barrier, every weak solution with initial data $p^{\mathrm{ini}} \le \overline{P}$ satisfies $p(t) \le \overline{P}$ for all $t > 0$, so the invasion stops: the infection never reaches the high-capacity region.

**No blocking for small variations.** Conversely, if $K'/K$ and $K''/K$ are small enough, a travelling-wave subsolution of the form $\phi_A(x - c_A t)$ propagates and converges to $1$ locally uniformly, so the invasion succeeds.

## Depends on

- [High-fecundity reduction of Wolbachia dynamics to a scalar equation with heterogeneous carrying capacity](high-fecundity-reduction-of-wolbachia-dynamics-with-heterogeneous-carrying-capacity.md)

## Expansion

A barrier is a stationary supersolution separating the invaded state from the uninfected region, so the comparison principle traps any solution starting below it. To construct one, solve on each piece: outside $[0, L]$, $-p'' = f(p)$ has the energy identity $\frac12 p'^2 + F(p) = \mathrm{const}$, fixing the phase-plane orbits towards $1$ on the left and towards $0$ on the right; inside $(0, L)$ the drift $2Cp'$ and source $C^2 g(p)$ dominate when $C$ is large. Inside the ramp, writing $w(p) = \frac12 p'^2$ as a function of $p$ turns the equation into the first-order problem $w' = 2C\sqrt{2w} - f(p) - C^2 g(p)$; with the endpoint value $\beta = s_f/s_h$ (a zero of $g$) fixed, existence reduces to finding $\alpha$ between $\arg\max g$ and $s_f/s_h$ at which $w$ matches the jump condition. Comparison with $-F(s_f/s_h - \tau) + C^2 g_\infty^2/8$ shows this matching succeeds once $C > 2\sqrt{2F(1)}/g_\infty$. Biologically, a sharp increase in mosquito carrying capacity creates a net flux of uninfected mosquitoes from the dense region that can halt a population-replacement front even though it would invade a homogeneous environment.

## Sources

- S. Latrach, N. Vauchelet and H. Zaag, *Blocking of bistable front propagation: Application to Wolbachia population replacement*, arXiv:2610.13497 (2026), Section 2.3 (barrier definition, main blocking theorem, comparison proposition) and Section 4 (no blocking for small variations; existence of stationary solutions and the bound on $C^*$; scaling of barriers in $L$). <https://doi.org/10.48550/arXiv.2610.13497>
