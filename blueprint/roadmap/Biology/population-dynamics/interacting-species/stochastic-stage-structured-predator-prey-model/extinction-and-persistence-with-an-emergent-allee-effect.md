# Extinction and persistence in a stochastic predator-prey model with an emergent Allee effect

**Model.** Juvenile prey $x$, adult prey $y$ and predators $z$ satisfy the Itô system

$$dx = \bigl(\beta y - \varphi(x)x - \mu_x x\bigr)dt - \sigma_x x\,dB_x, \qquad dy = \bigl(\varphi(x)x - \mu_y y - yz\bigr)dt - \sigma_y y\,dB_y,$$

$$dz = z(\alpha y - \mu_z)\,dt - \sigma_z z\,dB_z ,$$

with birth rate $\beta$, maturation function $\varphi$ (for persistence results $\varphi(x) = \kappa/(1+x)$, which saturates maturation and produces an emergent Allee effect), mortalities $\mu_x, \mu_y, \mu_z$, conversion $\alpha$, and independent Brownian motions with intensities $\sigma_x,\sigma_y,\sigma_z$.

**Theorem.** For initial data in $\mathbb{R}^3_{>0}$:
1. (Positivity) there is a unique global solution, remaining in $\mathbb{R}^3_{>0}$ almost surely.
2. (Stability of extinction) if $\mu_y \ge \beta$, the origin is stable in probability; if $\mu_x > \sigma_x^2/2$, $\mu_z > \sigma_z^2/2$ and $\bigl(\tfrac{\sigma_x^2}{2} - \mu_x\bigr)\bigl(\tfrac{\sigma_y^2}{2} - \mu_y\bigr) > \tfrac{\beta^2}{4}$, it is asymptotically stable in probability.
3. (Prey extinction) if $\beta < \min\{\mu_x, \mu_y\}$, then $x(t) + y(t) \to 0$ almost surely.
4. (Predator extinction) on the event $\{y(t) \to 0\}$, if it has positive probability, $z(t) \to 0$ almost surely.
5. (Prey persistence) under explicit parameter conditions and conditionally on an event $Z_M$ on which the predator density is controlled, $\mathbb{P}(\liminf x(t) > r) \ge \mathbb{P}(X > r)$ and likewise for $y$, for a random vector $(X,Y)$ supported in $\mathbb{R}^2_{>0}$; in particular both prey stages persist almost surely given $Z_M$.

## Expansion

Stability of the origin uses quadratic Lyapunov functions: the generator applied to a quadratic form picks up $\sigma^2$ terms from Itô's formula, and the determinant condition makes the resulting quadratic form negative definite. Prey extinction follows from the linear bound $d(x+y) \le (\beta - \min\{\mu_x,\mu_y\})(x+y)\,dt + \text{martingale}$, since the maturation and predation terms only move or remove mass. With saturating maturation, low juvenile density slows recruitment into the adult stage, so the origin can be attracting while a positive state is also stable, the hallmark of an Allee effect; noise can push trajectories across the threshold.

## Sources

- C. Granados, L. A. Valencia, "Persistence and extinction dynamics in a stochastic predator-prey model with emergent Allee effects", *Communication in Biomathematical Sciences* 9(1) (2026), 29–47, model (themodel), Theorems 3.1-3.6, <https://doi.org/10.5614/cbms.2026.9.1.3> (preprint arXiv:2503.17583).
