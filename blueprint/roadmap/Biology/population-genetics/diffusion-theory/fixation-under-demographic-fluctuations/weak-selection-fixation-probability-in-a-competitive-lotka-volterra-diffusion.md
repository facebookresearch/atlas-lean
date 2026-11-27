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

where $\psi$ does not depend on $p$ and solves the linear inhomogeneous second-order equation (Eq. 10)

$$0 = z + \frac{1}{M} + z\big((\beta - \gamma)d - z\big)\psi'(z) - \frac{3}{zM}\big((\beta + \gamma)d + z\big)\psi(z) + \frac{z}{2M}\big((\beta + \gamma)d + z\big)\psi''(z), \qquad z > 0,$$

namely the solution with $\psi(z) \to 0$ as $z \to 0^+$ and $\psi(z) \sim \ln z$ as $z \to \infty$.

**Lemma 1.** $\psi(z) > 0$ for all $z > 0$.

Consequences (Corollary 1 and Eq. 11):

- $\varphi(p^*, z) = p^*$: starting exactly at the coexistence frequency, fixation is neutral to first order.
- For arbitrary $a, c > 0$ and $p < p^*$, $\varphi > \varphi_{\mathrm{neu}}$ iff $b > d$, since $p(1-p)(1 - p/p^*) > 0$ for $0 < p < p^*$ and $\psi(z) > 0$; the fixation probability increases with $a$ (weaker self-competition of the mutant).
- Because $\psi > 0$, the initial population size $z$ affects the magnitude but not the sign of the selective effect.

## Expansion

The proof substitutes the ansatz into the transformed generator; under the stated smallness conditions all terms of second order in the perturbation drop out, the $p$- and $z$-dependence separate, and the remaining equation for $\psi$ is Eq. (10), a linear ODE in $z$ alone. Lemma 1 follows Lambert's argument for the logistic branching process: the substitution $h = -\psi'/\psi$ turns the homogeneous equation into a Riccati equation with a unique non-negative solution $h$, and variation of constants, with the two boundary behaviours fixing the free constants, gives $\psi$ as an iterated integral with positive integrand (Eq. 31). The equilibrium frequency follows from equating the two per-capita growth rates, $x/a + y/b = x/c + y/d$, which gives $y^*/x^* = \frac{bd}{ac}\cdot\frac{c-a}{b-d}$. Unlike Moran-type models with constant size, here neither type can grow without bound and both eventually go extinct, so fixation is defined by which type survives the other.

## Sources

- P. Czuppon, A. Traulsen, "Fixation probabilities in populations under demographic fluctuations", Journal of Mathematical Biology 77 (2018) 1233–1277, Section 2 (diffusion Eq. 4, generator Eq. 5) and Section 3 (Definition 1, Eqs. 6–8, neutral model, conditions (i)–(iv), Theorem 1 with Eqs. 9–11, Lemma 1, Corollary 1), with proofs in Appendices A–E, <https://doi.org/10.1007/s00285-018-1251-9> (PMC6153673).
