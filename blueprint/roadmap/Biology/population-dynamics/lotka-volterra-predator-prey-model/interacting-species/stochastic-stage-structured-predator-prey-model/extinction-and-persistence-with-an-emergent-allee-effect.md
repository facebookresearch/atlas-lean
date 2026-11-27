# Extinction and persistence in a stochastic predator-prey model with an emergent Allee effect

**Model.** Juvenile prey $x$, adult prey $y$ and predators $z$ satisfy the Itô system

$$dx = \bigl(\beta y - \varphi(x)x - \mu_x x\bigr)dt - \sigma_x x\,dB_x, \qquad dy = \bigl(\varphi(x)x - \mu_y y - yz\bigr)dt - \sigma_y y\,dB_y,$$

$$dz = z(\alpha y - \mu_z)\,dt - \sigma_z z\,dB_z ,$$

with birth rate $\beta>0$, a maturation function $\varphi:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ that is differentiable on $(0,\infty)$, satisfies $\lim_{x\to\infty}\varphi(x)=0$ and has $\sup_{x\ge0}\varphi(x)\le1$ (for the persistence result $\varphi(x) = \kappa/(1+x)$, $\kappa>0$, which saturates maturation and produces an emergent Allee effect), mortalities $\mu_x, \mu_y, \mu_z>0$, conversion efficiency $\alpha\in(0,1)$, and independent Brownian motions $B_x,B_y,B_z$ with intensities $\sigma_x,\sigma_y,\sigma_z>0$ (item 5 uses that the noise is nondegenerate). The bounds $\alpha<1$ and $\varphi\le1$ are used in the proofs of items 1 and 2 below.

**Theorem.** For initial data in $\mathbb{R}^3_{>0}$:
1. (Positivity) there is a unique global solution, remaining in $\mathbb{R}^3_{>0}$ almost surely.
2. (Stability of extinction) if $\mu_y \ge \beta$, the origin is stable in probability; if $\mu_x > \sigma_x^2/2$, $\mu_z > \sigma_z^2/2$ and $\bigl(\tfrac{\sigma_x^2}{2} - \mu_x\bigr)\bigl(\tfrac{\sigma_y^2}{2} - \mu_y\bigr) > \tfrac{\beta^2}{4}$, it is asymptotically stable in probability.
3. (Prey extinction) if $\beta < \min\{\mu_x, \mu_y\}$, then $x(t) + y(t) \to 0$ almost surely.
4. (Predator extinction) on the event $\{y(t) \to 0\}$, if it has positive probability, $z(t) \to 0$ almost surely.
5. (Prey persistence) Let $\varphi(x)=\kappa/(1+x)$, fix $M>0$, and let $Z_M=\{\sup_{t\ge0}z(t)\le M\}$ (predator density never exceeds $M$). Consider the auxiliary prey system, which replaces predation by the maximal rate $M$,

$$d\bar x=\Bigl(\beta\bar y-\frac{\kappa\bar x}{1+\bar x}-\mu_x\bar x\Bigr)dt-\sigma_x\bar x\,dB_x,\qquad d\bar y=\Bigl(\frac{\kappa\bar x}{1+\bar x}-(\mu_y+M)\bar y\Bigr)dt-\sigma_y\bar y\,dB_y .$$

If

$$\tfrac12\sigma_y^2<\mu_y+M\qquad\text{and}\qquad \frac{\kappa}{\beta}+\frac{\mu_x}{\beta}+\mu_y+M+\frac{\sigma_x^2}{2}+\frac{\sigma_y^2}{2\beta}<1,$$

the auxiliary system has a unique stationary distribution, the law of a random vector $(X,Y)$ supported in $\mathbb R^2_{>0}$, and for every $r>0$

$$\mathbb{P}\bigl(\liminf_{t\to\infty} x(t) > r \bigm| Z_M\bigr) \ge \mathbb{P}(X > r),\qquad \mathbb{P}\bigl(\liminf_{t\to\infty} y(t) > r \bigm| Z_M\bigr) \ge \mathbb{P}(Y > r);$$

in particular $\mathbb P(\liminf x(t)>0\mid Z_M)=\mathbb P(\liminf y(t)>0\mid Z_M)=1$. (The source prints the second condition, its (17), with an undefined constant $b$ in place of $\beta$; its appendix statement and the Lyapunov function $\beta^{-1}(x-\ln x)+y-\ln y+\tfrac12y^2$ used in the proof identify $b=\beta$.)

## Expansion

Stability of the origin uses quadratic Lyapunov functions: the generator applied to a quadratic form picks up $\sigma^2$ terms from Itô's formula, and the determinant condition makes the resulting quadratic form negative definite. Prey extinction follows from the linear bound $d(x+y) \le (\beta - \min\{\mu_x,\mu_y\})(x+y)\,dt + \text{martingale}$, since the maturation and predation terms only move or remove mass. With saturating maturation, low juvenile density slows recruitment into the adult stage, so the origin can be attracting while a positive state is also stable, the hallmark of an Allee effect; noise can push trajectories across the threshold.

## Sources

- C. Granados, L. A. Valencia, "Persistence and extinction dynamics in a stochastic predator-prey model with emergent Allee effects", *Communication in Biomathematical Sciences* 9(1) (2026), 29–47, the stochastic model of Section 1, Theorems 3.1-3.6, auxiliary system (16), conditions (17) and the appendix theorem on its stationary distribution, <https://doi.org/10.5614/cbms.2026.9.1.3> (preprint arXiv:2503.17583).
