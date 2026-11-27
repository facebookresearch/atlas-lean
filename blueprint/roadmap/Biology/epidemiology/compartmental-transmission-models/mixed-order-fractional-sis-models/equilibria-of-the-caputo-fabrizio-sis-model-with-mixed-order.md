# Equilibria of the Caputo–Fabrizio SIS model with mixed fractional order

**Model.** For $\alpha \in [0,1)$ and $u \in H^1$, the Caputo–Fabrizio derivative is

$$
{}^{\mathrm{CF}}D_t^{\alpha} u(t) = \frac{M(\alpha)}{1-\alpha}\int_0^t u'(\tau)\,e^{-\frac{\alpha}{1-\alpha}(t-\tau)}\,d\tau,
$$

with a scaling factor $M(\alpha) \ge 0$, $M(0) = M(1) = 1$. Consider the SIS model in which only the susceptible class evolves with fractional order:

$$
{}^{\mathrm{CF}}D_t^{\alpha} S = -\Big(\frac{\beta S}{S+I} - \gamma\Big) I, \qquad I' = \Big(\frac{\beta S}{S+I} - \gamma\Big) I, \qquad S(0) = S_0,\ I(0) = I_0,
$$

with $\beta, \gamma > 0$, $S_0, I_0 \ge 0$, $S_0 + I_0 > 0$, under the assumptions $\gamma < \alpha/(1-\alpha)$ and $M(\alpha) \ge \alpha$. Unlike the classical case $\alpha = 1$, the total population $N = S + I$ is not conserved.

**Theorem (reduction to one equation).** Let

$$
P_\alpha = M(\alpha)S_0 + \alpha I_0 + (1-\alpha)\Big(\beta - \gamma - \frac{\beta I_0}{S_0 + I_0}\Big) I_0.
$$

Then the quantity $M(\alpha)S + \alpha I + (1-\alpha)\big(\beta - \gamma - \frac{\beta I}{S+I}\big)I$ is conserved and equals $P_\alpha$. A pair of nonnegative absolutely continuous functions $(S, I)$ solves the system if and only if $S(t) = g_\alpha(I(t))$, where $g_\alpha$ is the nonnegative root of this quadratic conservation law (an explicit, convex function of $I$ determined by $\alpha, \beta, \gamma, M(\alpha), P_\alpha$), and $I$ solves the scalar equation

$$
I' = \Big(\beta - \gamma - \frac{\beta I}{g_\alpha(I) + I}\Big) I, \qquad I(0) = I_0.
$$

For $\alpha = 1$ this reduces to $S = N - I$.

**Proposition (equilibria and global stability).** The equilibria of the scalar equation are $0$ and

$$
E_\alpha = \frac{(\beta - \gamma)\,P_\alpha}{\alpha(\beta - \gamma) + M(\alpha)\gamma}.
$$

With $R = \beta/\gamma$: if $R > 1$, then $E_\alpha > 0$ and

$$
I(t) \to E_\alpha, \qquad S(t) \to \frac{\gamma}{\beta - \gamma}E_\alpha = \frac{\gamma P_\alpha}{\alpha(\beta-\gamma) + M(\alpha)\gamma};
$$

if $R \le 1$, then $I(t) \to 0$ and $S(t) \to P_\alpha / M(\alpha)$.

**Proposition (monotonicity of the total population).** Let $S_0, I_0 > 0$. If $R > 1$ and $0 < I_0 < E_\alpha$, then $N(t)$ increases strictly to $N_\alpha = \frac{\beta}{\beta - \gamma}E_\alpha$. If $R > 1$ and $I_0 > E_\alpha$, or if $R \le 1$, then $N(t)$ decreases strictly to its limit. In particular the long-run total population determines the fractional order: for $M \equiv 1$, $N_0 = S_0 + I_0$ and $N(t) \to N_\infty$ with $R > 1$,

$$
\alpha = 1 - \frac{(N_\infty - N_0)N_0\beta}{\beta I_0 S_0 - \beta N_0(I_0 + \gamma I_0 - N_\infty) - \gamma N_0 N_\infty},
$$

and $\alpha = 1$ if and only if $N_\infty = N_0$.

## Expansion

The kernel is exponential, so $\frac{d}{dt}{}^{\mathrm{CF}}D_t^{\alpha}u = \frac{M(\alpha)}{1-\alpha}u' - \frac{\alpha}{1-\alpha}{}^{\mathrm{CF}}D_t^{\alpha}u$. Differentiating the $S$ equation therefore gives an ordinary differential system with the first integral above. Solving it for $S$ (the discriminant of the quadratic is negative, so $g_\alpha$ is defined on all of $\mathbb{R}$) reduces the problem to a scalar autonomous equation, whose positive equilibrium is found by solving $\beta g_\alpha(I) = \gamma(g_\alpha(I) + I)$ together with the conservation law. The function $(I - x_R)^2$, with $x_R$ the relevant equilibrium, is a Lyapunov function on $[0, \infty)$. Since $N' = I'(1 + g_\alpha'(I))$ and convexity of $g_\alpha$ controls the sign of $1 + g_\alpha'$ along the trajectory, $N$ moves in the same direction as $I$.

## Sources

- Caterina Balzotti, Mirko D’Ovidio, Anna Chiara Lai, Paola Loreti, "Effects of Fractional Derivatives with Different Orders in SIS Epidemic Models", Computation 9 (2021), 89, <https://doi.org/10.3390/computation9080089>. Published version of arXiv:2107.02877, cited next; locators there refer to the arXiv version.
- Caterina Balzotti, Mirko D'Ovidio, Anna Chiara Lai, Paola Loreti, *Effects of fractional derivatives in epidemic models*, arXiv 2021. Section 3.1: Theorem 2 (reduction to a scalar ODE), Proposition 1 (equilibria and global stability), Proposition 2 (monotonicity of $N$ and recovery of $\alpha$). <https://doi.org/10.48550/arXiv.2107.02877>
