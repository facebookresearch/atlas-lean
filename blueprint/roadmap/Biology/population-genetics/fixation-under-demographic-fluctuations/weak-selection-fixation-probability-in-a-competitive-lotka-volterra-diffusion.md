# Weak-selection fixation probability in a competitive Lotka–Volterra diffusion

**Model.** Two types $X$ (mutant) and $Y$ (resident) with common per-capita birth rate $\beta$ and death rate $\gamma$ ($\beta > \gamma$) compete; $a, b, c, d > 0$ are inverse competition strengths, so that an $X$ individual dies from competition at per-capita rate $x/a + y/b$ and a $Y$ individual at rate $x/c + y/d$. With rescaled densities $x = X/M$, $y = Y/M$ ($M$ a large system-size parameter), the diffusion approximation is
$$\begin{aligned}
dx &= x\Big(\beta - \gamma - \frac{x}{a} - \frac{y}{b}\Big)dt + \sqrt{\frac{x}{M}\Big(\beta + \gamma + \frac{x}{a} + \frac{y}{b}\Big)}\, dW_1, \\
dy &= y\Big(\beta - \gamma - \frac{x}{c} - \frac{y}{d}\Big)dt + \sqrt{\frac{y}{M}\Big(\beta + \gamma + \frac{x}{c} + \frac{y}{d}\Big)}\, dW_2,
\end{aligned}$$
with independent Brownian motions $W_1, W_2$. $X$ *fixes* if $y(t) = 0$ while $x(t) > 0$ at some time $t$. In the coordinates $p = x/(x+y)$ (mutant frequency) and $z = x + y$ (population size), the deterministic interior equilibrium has frequency

$$p^* = \frac{b - d}{(b-d) + \frac{bd}{ac}(c - a)}, \qquad \text{i.e.}\quad \frac{1}{p^*} = 1 + \frac{bd}{ac}\cdot\frac{c-a}{b-d}.$$

The fixation probability $\varphi(p, z)$ solves $\tilde G\varphi = 0$ for the generator $\tilde G$ of $(p, z)$ with $\varphi(0, z) = 0$ and $\varphi(1, z) = 1$. In the neutral case $a = b = c = d$, $\varphi_{\mathrm{neu}}(p, z) = p$.

**Theorem (weak selection).** Suppose the competition matrix is a small perturbation of a neutral one, in the sense that $(1 - d/b)^2$, $(1 - d/b)(2 - d/c - d/b)$, $(1 - d/b)(1 + d/a - 2d/b)$ and $(1 - d/b)(1/p^* - 2)$ are all negligible. Then

$$\varphi(p, z) = p + p(1-p)\Big(1 - \frac{p}{p^*}\Big)\Big(1 - \frac{d}{b}\Big)\psi(z) + O\Big(\big(1 - \tfrac{d}{b}\big)^2\Big),$$

where $\psi$ does not depend on $p$, solves a linear second-order ODE in $z$, and does not change sign. Consequences:

- $\varphi(p^*, z) = p^*$: starting exactly at the coexistence frequency, fixation is neutral to first order.
- For $p < p^*$, $\varphi > \varphi_{\mathrm{neu}}$ iff $b > d$; the fixation probability increases with $a$ (weaker self-competition of the mutant).
- The initial population size $z$ affects the magnitude but not the sign of the selective effect.

## Expansion

The proof substitutes the ansatz into the transformed generator; under the stated smallness conditions all terms of second order in the perturbation drop out, the $p$- and $z$-dependence separate, and the remaining equation for $\psi$ is a linear ODE in $z$ alone. The equilibrium frequency follows from equating the two per-capita growth rates, $x/a + y/b = x/c + y/d$, which gives $y^*/x^* = \frac{bd}{ac}\cdot\frac{c-a}{b-d}$. Unlike Moran-type models with constant size, here neither type can grow without bound and both eventually go extinct, so fixation is defined by which type survives the other.

## Sources

- P. Czuppon, A. Traulsen, "Fixation probabilities in populations under demographic fluctuations", Journal of Mathematical Biology 77 (2018) 1233–1277, Section 2 (diffusion Eq. 4, generator Eq. 5, Definition 1, Eqs. 6–8, neutral model) and Section 3 (conditions (i)–(iv), Theorem 1, Eqs. 9–11, Corollary on competition parameters), with proofs in Appendices A–D, <https://doi.org/10.1007/s00285-018-1251-9> (PMC6153673).
