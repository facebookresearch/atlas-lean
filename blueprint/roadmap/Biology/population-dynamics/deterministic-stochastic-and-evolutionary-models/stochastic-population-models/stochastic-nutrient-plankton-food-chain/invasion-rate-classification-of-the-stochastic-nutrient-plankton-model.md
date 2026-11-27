# Invasion-rate classification of the stochastic nutrient–phytoplankton–zooplankton model

**Model.** Let $X, Y, Z \ge 0$ be the densities of a limiting nutrient, phytoplankton and herbivorous zooplankton, driven by independent Brownian motions $W_1, W_2, W_3$:

$$dX = \big[\Lambda - F_1(X,Y)XY - \alpha_1 X + \alpha_4 Y + \alpha_5 Z\big]dt + \sigma_1 X\,dW_1,$$

$$dY = \big[F_1(X,Y)XY - F_2(Y,Z)YZ - \alpha_2 Y\big]dt + \sigma_2 Y\,dW_2,$$

$$dZ = \big[F_2(Y,Z)YZ - \alpha_3 Z\big]dt + \sigma_3 Z\,dW_3.$$

Here $\Lambda > 0$ is the nutrient input, $\alpha_1$ the nutrient washout, $\alpha_2, \alpha_3$ the loss rates of the plankton, and $\alpha_4 < \alpha_2$, $\alpha_5 < \alpha_3$ the recycling rates. The functional responses $F_1, F_2$ are bounded by $L$, $F_1(u,v)u$ and $F_2(u,v)u$ are Lipschitz with constant at most $L$, and $u \mapsto F_1(u,0)u$ is nondecreasing. (With $F_1 \equiv a$, $F_2 \equiv b$ this is the classical Lotka–Volterra-type nutrient–plankton chain.)

**Invasion rates.** The nutrient-only process $d\hat X = (\Lambda - \alpha_1\hat X)dt + \sigma_1\hat X\,dW_1$ has a unique invariant law $\mu_1$, an inverse Gamma distribution. Define

$$\lambda_1 = \int_{[0,\infty)} F_1(u,0)\,u\,\mu_1(du) - \alpha_2 - \frac{\sigma_2^2}{2}$$

(for $F_1 \equiv a$, $\lambda_1 = a\Lambda/\alpha_1 - \alpha_2 - \sigma_2^2/2$). If $\lambda_1 > 0$ the nutrient–phytoplankton subsystem has a unique invariant law $\mu_{12}$ on $(0,\infty)^2$, and

$$\lambda_2 = \int_{(0,\infty)^2} F_2(y,0)\,y\,\mu_{12}(dx\,dy) - \alpha_3 - \frac{\sigma_3^2}{2},$$

the per-capita growth rate of rare zooplankton averaged over $\mu_{12}$.

**Theorem.** For every initial value in $\mathbb{R}_+^3$ there is a unique global solution that stays in $\mathbb{R}_+^3$, with $X(t) > 0$ for $t > 0$, and it is a Feller–Markov process. For initial values in $(0,\infty)^3$:
1. if $\lambda_1 < 0$, then almost surely $\frac{\ln Y(t)}{t} \to \lambda_1$ and $\frac{\ln Z(t)}{t} \to -\alpha_3 - \frac{\sigma_3^2}{2}$ (both plankton die out);
2. if $\lambda_1 > 0 > \lambda_2$, then almost surely $\frac{\ln Z(t)}{t} \to \lambda_2$ and the normalized occupation measures of $(X,Y)$ converge weakly to $\mu_{12}$ (zooplankton dies out, phytoplankton persists);
3. if $\lambda_1 > 0$ and $\lambda_2 > 0$, there is a unique invariant probability measure $\mu^\circ$ on $(0,\infty)^3$ and, for some $q_0 > 1$ and all $1 \le \tilde q < q_0$,

$$\lim_{t\to\infty} t^{\tilde q - 1}\,\big\|P_t(\mathbf{s}, \cdot) - \mu^\circ\big\|_{TV} = 0.$$

## Proof sketch

$\lambda_1$ is the long-run per-capita growth rate of a rare phytoplankton population living on the nutrient at its own stochastic equilibrium, corrected by the Itô term $-\sigma_2^2/2$; $\lambda_2$ is the same for rare zooplankton invading the nutrient–phytoplankton equilibrium. The signs of these invasion rates decide which species persist, as in general stochastic persistence theory for Kolmogorov systems. The difficulty here is that recycling ($\alpha_4, \alpha_5$) breaks the usual dissipativity, so the authors build Lyapunov-type functions that give only polynomial, not exponential, moment bounds; this is why convergence to $\mu^\circ$ is stated at a polynomial rate.

## Sources

- Alexandru Hening, Nguyen Trong Hieu, Dang Hai Nguyen and Nhu Ngoc Nguyen, "Stochastic nutrient-plankton models", *Journal of Differential Equations* 376 (2023), 370–405, <https://doi.org/10.1016/j.jde.2023.08.017>. Preprint version: arXiv:2303.07534 (2023), model and Assumption 1.1, definitions of $\lambda_1, \lambda_2$ and Theorems 1.1–1.4 with Proposition 1.1 (Section 1), Lemma 2.2 (inverse Gamma invariant law), <https://doi.org/10.48550/arXiv.2303.07534>.
