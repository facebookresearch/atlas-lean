# Exact simulation of the Wright–Fisher diffusion with selection

Jenkins and Spanò (2017, Section 5) simulate exactly from the one-dimensional Wright–Fisher diffusion with drift $\gamma$ by rejection, with the neutral diffusion of drift $\alpha(x) = \frac12[\theta_1(1 - x) - \theta_2x]$, $\theta_1, \theta_2 > 0$, as candidate, since its values at finitely many times can be sampled exactly. A drift $\gamma$ belongs to their class if (WF1) the target law is absolutely continuous with respect to the candidate, with Radon–Nikodým derivative given by Girsanov's formula

$$\frac{dWF_{\gamma,x_0}}{dWF_{\alpha,x_0}}(X) = \exp\Bigl\{\int_0^T\frac{\gamma(X_t) - \alpha(X_t)}{X_t(1 - X_t)}\,dX_t - \frac12\int_0^T\frac{\gamma^2(X_t) - \alpha^2(X_t)}{X_t(1 - X_t)}\,dt\Bigr\},$$

(WF2) $\gamma$ is continuously differentiable on $(0, 1)$, (WF3) the function $\tilde\phi(x) = \frac12\bigl[(\gamma^2(x) - \alpha^2(x))/(x(1 - x)) + \gamma'(x) - \alpha'(x) - (\gamma(x) - \alpha(x))(1 - 2x)/(x(1 - x))\bigr]$ is bounded, $\tilde\phi^- \le \tilde\phi \le \tilde\phi^+$, and (WF4) $\tilde A(x) = \int_0^x(\gamma(z) - \alpha(z))/(z(1 - z))\,dz$ is bounded above by $\tilde A^+$. By Itô's lemma the derivative is then proportional to $\exp\{\tilde A(X_T) - \tilde A^+\}\exp\{-\int_0^T[\tilde\phi(X_t) - \tilde\phi^-]\,dt\}$ (equation (24)), a probability. Algorithm 7 simulates a Poisson point process of unit intensity on $[0, T] \times [0, M]$, $M = \tilde\phi^+ - \tilde\phi^-$ (equivalently, $N \sim \mathrm{Poisson}(MT)$ points placed independently and uniformly on the rectangle; when $M = 0$ the Poisson test accepts automatically), and the candidate at its times and at $T$, and accepts when no point lies below the graph of $t \mapsto \tilde\phi(X_t) - \tilde\phi^-$ (every point has height at least that value, an event of probability $\exp\{-\int_0^T[\tilde\phi(X_t) - \tilde\phi^-]\,dt\}$ given the path) and an independent uniform variable is below $\exp\{\tilde A(X_T) - \tilde A^+\}$; accepted skeletons are exact samples of the target. By Proposition 6, every drift $\gamma(x) = \alpha(x) + x(1 - x)\eta(x)$ with $\theta_1, \theta_2 > 0$ and $\eta$ continuously differentiable on $[0, 1]$ is in the class; this includes diploid selection, with $\eta(x)$ proportional to $x + h(1 - 2x)$, and frequency-dependent selection.

## Depends on

- [Exact simulation of the Wright–Fisher diffusion](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/exact-simulation-of-the-wright-fisher-diffusion.md)
- [Girsanov's theorem for a constant drift](../../../../Probability/stochastic-calculus/has-law-sub-drift-with-density.md)

## Expansion

1. The neutral candidate with $\theta_1, \theta_2 > 0$ and its exact sampling at finitely many times.
2. Girsanov's formula for the target relative to the candidate, and its rewriting with $\tilde A$ and $\tilde\phi$ by Itô's lemma.
3. The Poisson acceptance event, its probability, and the law of accepted skeletons.
4. Proposition 6: drifts $\alpha + x(1 - x)\eta$ with $\eta$ continuously differentiable satisfy the four conditions.
5. Selected bridges by rejection from the neutral bridge, as a separate statement.

## Sources

- P. A. Jenkins and D. Spanò, Exact simulation of the Wright–Fisher diffusion, Ann. Appl. Probab. 27 (2017), 1478–1509, Sections 5.1–5.3, conditions (WF1)–(WF4), equations (23)–(25), Algorithm 7 and Proposition 6. <https://doi.org/10.1214/16-AAP1236> <https://arxiv.org/abs/1506.06998>
