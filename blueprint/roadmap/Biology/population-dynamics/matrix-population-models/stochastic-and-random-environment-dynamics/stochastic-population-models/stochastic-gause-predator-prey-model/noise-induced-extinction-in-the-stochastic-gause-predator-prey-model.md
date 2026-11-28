# Noise-induced extinction in the stochastic Gause predator–prey model

In nondimensional form, consider prey $x$ with logistic growth, predators $y$, and independent multiplicative white noise:

$$
dx=\big(x(1-x)-\varphi(x)y\big)\,dt+\sigma_xx\,dB_x,\qquad dy=\big(\beta\varphi(x)y-\delta y\big)\,dt+\sigma_yy\,dB_y.
$$

Here $\beta,\delta,\sigma_x,\sigma_y>0$, and the functional response $\varphi$ is continuous and nonnegative with $\varphi(0)=0$ and $\sup_{x>0}\varphi(x)/x\le1$ (sub-linear). Let $\mathcal E_x,\mathcal E_y$ be the events $x(t)\to0$ and $y(t)\to0$.

1. **Well-posedness.** For every initial value in $\mathbb R^2_+$ there is a.s. a unique global solution in $\mathbb R^2_+$. For $\theta_1,\theta_2>0$ with $\theta_1+\theta_2<\tfrac12$, the moment $\mathbb E[x^{\theta_1}y^{\theta_2}]$ is bounded uniformly in time, with explicit constants.
2. Prey extinction forces predator extinction: $\mathbb P(\mathcal E_y\mid\mathcal E_x)=1$.
3. **Prey extinction.** If $\sigma_x^2>2$, then $\mathbb P(\mathcal E_x)=1$.
4. **Predator extinction.** If $\varphi\le1$ (bounded response) and $\sigma_y^2>2(\beta-\delta)$, then $\mathbb P(\mathcal E_y)=1$.
5. **Prey after predator loss.** If $\sigma_x^2<2$, then on $\mathcal E_y$ the prey converges in distribution to $\tilde X>0$ with density

$$
f_{\tilde X}(x)\propto\frac{1}{\sigma_x^2x^2}\exp\Big(\frac{2(1-x+\log x)}{\sigma_x^2}\Big),\qquad x>0,
$$

the stationary law of the stochastic logistic equation.

So noise can drive either species extinct even when the deterministic Gause model has a stable coexistence equilibrium.

## Proof sketch

By Itô's formula, $d\log x=(1-x-\varphi(x)y/x-\sigma_x^2/2)\,dt+\sigma_x\,dB_x$. Since the drift is at most $1-\sigma_x^2/2$, the strong law for Brownian motion gives $\limsup t^{-1}\log x\le1-\sigma_x^2/2<0$. Likewise $d\log y\le(\beta-\delta-\sigma_y^2/2)\,dt+\sigma_y\,dB_y$ when $\varphi\le1$. Once $y\to0$, the prey equation is asymptotically the stochastic logistic SDE, whose scale and speed densities give the stated gamma-type law.

## Related topics

- [Lotka–Volterra predator–prey model](../../../../lotka-volterra-predator-prey-model/README.md)

## Sources

- Andrés Sanchéz, Leon A. Valencia and Jorge M. Ramirez Osorio, "The Stochastic Gause Predator-Prey model: Noise-induced extinctions and invariance", *Mathematical Biosciences and Engineering* 22 (2025), 1999–2019, <https://doi.org/10.3934/mbe.2025073>. Preprint version: arXiv:2409.05237 (2024), system (eq_StochGause), Theorems 1–2, Proposition 3, Theorems 4–6, <https://doi.org/10.48550/arXiv.2409.05237>.
