# Periodic orbit of a periodically forced linear difference equation

Let $p \ge 1$ be an integer period, $\Upsilon(t)$ a nonnegative $\eta \times \eta$ matrix and $\Lambda(t) \in \mathbb R^\eta_{\ge 0}$ for $t \in \mathbb N$, both $p$-periodic: $\Upsilon(t+p) = \Upsilon(t)$, $\Lambda(t+p) = \Lambda(t)$. Consider

$$x(t+1) = \Upsilon(t)\, x(t) + \Lambda(t), \qquad x(0) = x_0 .$$

Define the transition products $\Phi(t,s) = \Upsilon(t-1)\Upsilon(t-2)\cdots\Upsilon(s)$ for $t > s$, $\Phi(s,s) = I$, and the monodromy matrix $\Phi = \Phi(p, 0)$.

**Theorem.** If every eigenvalue of $\Phi$ lies strictly inside the unit circle, i.e. $\rho(\Phi) < 1$, then the system has a unique $p$-periodic solution $x^*$, with initial value

$$x^*(0) = (I - \Phi)^{-1} \sum_{s=0}^{p-1} \Phi(p, s+1)\, \Lambda(s),$$

and every solution satisfies $x(t) - x^*(t) \to 0$ geometrically as $t \to \infty$. If $\Lambda \ge 0$ and $\Upsilon \ge 0$, then $x^* \ge 0$.

In the seasonal model of malaria in mosquitoes, $x(t)$ stacks the daily numbers of host-seeking mosquitoes that are uninfected, infected or infective, together with the cohorts still in their feeding cycle or in the parasite's development period. $\Lambda(t)$ is the seasonal emergence of new adults, and $\Upsilon(t)$ collects the daily probabilities of staying host-seeking, of feeding and surviving a feeding cycle, and of becoming infected. These depend periodically on host availability. Periodic field quantities, such as the parous, delayed-oocyst and sporozoite proportions and the entomological inoculation rate, are then ratios of components of $x^*$.

## Expansion

Iterating the recursion over one period gives the affine map $x(t+p) = \Phi\, x(t) + \sum_{s=0}^{p-1} \Phi(p, s+1)\Lambda(s)$ at times $t \equiv 0 \pmod p$. A $p$-periodic solution is a fixed point of this map. When $\rho(\Phi) < 1$, $I - \Phi$ is invertible, so the fixed point exists and is unique, and the homogeneous equation has no nontrivial periodic solution. The difference $e(t) = x(t) - x^*(t)$ solves the homogeneous equation, so $e(kp) = \Phi^k e(0) \to 0$ geometrically. Nonnegativity follows from the Neumann series $(I - \Phi)^{-1} = \sum_{j \ge 0} \Phi^j$, whose terms are all nonnegative. In the malaria application the spectral-radius condition is not proved in general but is checked numerically for each parameter set. It expresses that, on average over a year, mosquitoes die faster than the feeding cycle returns them.

## Sources

- N. Chitnis, D. Hardy, T. Smith, "A periodically-forced mathematical model for the seasonal dynamics of malaria in mosquitoes", *Bulletin of Mathematical Biology* (2012), Section 2 (model (1a)–(1b) and (2a)–(2c), Eq. (5), Theorem 2.1 with proof via Cushing's theorem on periodic difference equations) and Section 3 (field-measurable quantities, Eqs. (9a)–(10)), <https://doi.org/10.1007/s11538-011-9710-0> (PMC3339865).
