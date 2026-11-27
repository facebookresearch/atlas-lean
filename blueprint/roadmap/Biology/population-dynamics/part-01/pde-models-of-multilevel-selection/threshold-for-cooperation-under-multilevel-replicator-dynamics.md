# Threshold for cooperation under multilevel replicator dynamics

**Model.** Groups contain cooperators (fraction $x$) and defectors; individuals reproduce at rates $\pi_C(x), \pi_D(x)$ and groups at rate $G(x)$, all continuously differentiable on $[0,1]$, with an individual advantage to defect $\pi_D(x) > \pi_C(x)$ and a collective advantage $G(1) > G(0)$. In the limit of many large groups, the density $f(t, x)$ of group compositions satisfies

$$\partial_t f(t, x) = -\partial_x\big[x(1-x)\big(\pi_C(x) - \pi_D(x)\big) f(t, x)\big] + \lambda\, f(t, x)\Big[G(x) - \int_0^1 G(y) f(t, y)\, dy\Big],$$

where $\lambda > 0$ is the relative strength of among-group to within-group selection. Characteristics follow the within-group replicator equation $\dot x = x(1-x)(\pi_C - \pi_D)$, and along them $f$ is multiplied by $\exp\big(\lambda\int_0^t [G - \langle G\rangle_{f(s,\cdot)}]\,ds\big)$.

**Hölder exponent.** The initial density $f_0$ has Hölder exponent $\theta > 0$ at $x = 1$ if $\int_{1-y}^{1} f_0(z)\,dz \,/\, y^{\Theta}$ tends to $0$ for $\Theta < \theta$, to a positive constant for $\Theta = \theta$ and to $\infty$ for $\Theta > \theta$ as $y \to 0$ (e.g. $f_0(x) = \theta(1-x)^{\theta-1}$); small $\theta$ means many nearly fully cooperative groups initially.

**Theorem.** Let

$$\lambda^* = \frac{\theta\,\big(\pi_D(1) - \pi_C(1)\big)}{G(1) - G(0)} .$$

If $\lambda \le \lambda^*$, $f(t, \cdot)$ converges to $\delta_0$ (all groups become pure defectors). If $\lambda > \lambda^*$, $f(t, \cdot)$ converges to a steady-state density $f_\theta^\lambda$ with positive cooperation, and the mean collective payoff converges to

$$\langle G\rangle_{f_\theta^\lambda} = G(1) - \frac{\theta}{\lambda}\big(\pi_D(1) - \pi_C(1)\big) = \frac{\lambda^*}{\lambda} G(0) + \Big(1 - \frac{\lambda^*}{\lambda}\Big) G(1).$$

**Shadow of lower-level selection.** The long-run mean payoff never exceeds $G(1)$, even as $\lambda \to \infty$. For the pairwise game with payoffs $b - c + d$ (mutual cooperation), $-c$, $b$, $0$, one has $\pi_C(x) = (b+d)x - c$, $\pi_D(x) = bx$, $G(x) = (b-c)x + dx^2$, a prisoner's dilemma for $c - b < d < c$, and $\lambda^*_{PD} = \theta(c - d)/(b - c + d)$. If $d < -(b-c)/2$, $G$ is maximized at the interior composition $x^* = (b-c)/(-2d) < 1$, which multilevel selection can never attain.

## Expansion

The threshold balances the two forces at the all-cooperator composition: near $x = 1$, within-group selection drains groups toward defection at rate $\pi_D(1) - \pi_C(1)$ (the linearization of the replicator vector field at $x = 1$), while among-group selection amplifies near-cooperative groups at rate $\lambda(G(1) - \langle G\rangle)$, which is at most $\lambda(G(1) - G(0))$ when the population is mostly defectors. The density of groups within distance $y$ of $x = 1$ scales like $y^\theta$, and the characteristics push mass away from $x = 1$ exponentially, so mass near full cooperation persists iff the amplification beats $\theta$ times the drain, i.e. $\lambda > \lambda^*$. At steady state the same balance pins the mean payoff: $\lambda(G(1) - \langle G\rangle) = \theta(\pi_D(1) - \pi_C(1))$. Because the PDE favours groups only through comparison with $G(1)$ at the within-group equilibrium $x = 1$, an interior payoff optimum is invisible to among-group selection.

## Sources

- D. B. Cooney, S. A. Levin, Y. Mori, J. B. Plotkin, "Evolutionary dynamics within and among competing groups", Proceedings of the National Academy of Sciences USA 120 (2023) e2216186120, equations [2]–[12] and [14] (PDE [5], characteristic representation [6]–[7], Hölder exponent [8], threshold [9], steady-state payoff [10]–[12]), with Proposition 2.1 of the SI Appendix, <https://doi.org/10.1073/pnas.2216186120>.
