# MINDy neural mass model and its transfer function

**Model.** For $N$ brain regions with activity vector $x_t \in \mathbb{R}^N$, the Mesoscale Individualized Neurodynamic (MINDy) model is

$$\dot x = W\,\psi_\alpha(x_t) - D\,x_t + \varepsilon_t,$$

fitted in the discrete-time form $x_{t+\Delta t} - x_t = \big(W\psi_\alpha(x_t) - Dx_t + \varepsilon_t\big)\Delta t$ with $\Delta t$ the sampling interval. Here $W \in \mathbb{R}^{N\times N}$ is the effective connectivity, $D = \operatorname{diag}(D_1,\dots,D_N)$ with $D_i > 0$ the regional decay rates, $\varepsilon_t$ process noise independent across regions, and $\psi_\alpha$ acts componentwise with a region-specific curvature $\alpha_i > 0$:

$$\psi_{\alpha}(x) = \sqrt{\alpha^2 + \left(bx + \tfrac12\right)^2} - \sqrt{\alpha^2 + \left(bx - \tfrac12\right)^2},$$

where $b > 0$ is a global hyperparameter.

**Properties of the transfer function.** For every $\alpha > 0$ and $b > 0$:

1. $\psi_\alpha$ is odd, smooth and strictly increasing, with $\psi_\alpha(x) \to \pm 1$ as $x \to \pm\infty$;
2. $\psi_\alpha'(0) = b\big/\sqrt{\alpha^2 + \tfrac14}$, so smaller $\alpha$ gives a steeper, more switch-like response;
3. $x = 0$ is an equilibrium of the noise-free model, with Jacobian $W\,\operatorname{diag}\big(b/\sqrt{\alpha_i^2 + 1/4}\big) - D$.

## Expansion

Oddness follows by swapping the two square roots when $x \mapsto -x$. Writing $u_\pm = bx \pm \tfrac12$, the derivative is $b\big(u_+/\sqrt{\alpha^2+u_+^2} - u_-/\sqrt{\alpha^2+u_-^2}\big)$, positive because $u \mapsto u/\sqrt{\alpha^2+u^2}$ is strictly increasing; for large $|x|$ each root is $|u_\pm| + O(1/|x|)$, so the difference tends to $u_+ - u_- = 1$ in sign. Region-specific $\alpha_i$ and $D_i$ let the model absorb local heterogeneity in gain and time constant, so that $W$ is not forced to explain differences that are really local; the fitted models are not trivially linear, since their nonlinearity produces topologically distinct dynamics.

## Sources

- Singh MF, Braver TS, Cole MW, Ching S, "Estimation and validation of individualized dynamic brain models with resting state fMRI", Neuroimage (2020), Section 2.1, Eqs. (1)–(3), <https://doi.org/10.1016/j.neuroimage.2020.117046>, PMCID PMC7875185.
