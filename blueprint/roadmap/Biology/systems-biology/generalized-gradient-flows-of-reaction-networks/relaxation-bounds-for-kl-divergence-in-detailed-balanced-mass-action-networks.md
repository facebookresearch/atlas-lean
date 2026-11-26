# Relaxation bounds for the KL divergence in detailed-balanced mass-action networks

Consider a reversible mass-action network on $N$ species with $M$ reaction pairs, stoichiometric matrix $S \in \mathbb{Z}^{N \times M}$ with nonzero singular values $\sigma_1 \ge \dots \ge \sigma_{\operatorname{rk}(S)} > 0$, forward and backward fluxes $j^\pm_r(x)$, and a detailed-balanced (equilibrium) state $\hat x > 0$. The rate equation $\dot x = S\,(j^+(x) - j^-(x))$ is a **generalized gradient flow**:

$$\dot x_t = -S\, \partial_f \Psi^*_{x_t}\big(f(x_t)\big), \qquad f(x) = S^\top \partial_x D_{\mathrm{KL}}(x \,\|\, \hat x) = S^\top \log \frac{x}{\hat x} = \log \frac{j^+(x)}{j^-(x)},$$

where $D_{\mathrm{KL}}(x\|y) = \sum_i \big(x_i \log (x_i/y_i) - x_i + y_i\big)$ is the generalized KL divergence, $f$ is the thermodynamic force and $\Psi^*_x$ is a dissipation function. One admissible choice is the *quadratic dissipation* $\Psi^*_x(f) = \sum_r \omega_{\log,r}(x)\, f_r^2/2$ with the logarithmic-mean activity

$$\omega_{\log,r}(x) = \frac{j^+_r(x) - j^-_r(x)}{\log j^+_r(x) - \log j^-_r(x)}.$$

Along solutions $\tfrac{d}{dt} D_{\mathrm{KL}}(x_t\|\hat x) = -\langle \partial_f \Psi^*_{x_t}(f(x_t)), f(x_t)\rangle \le 0$ (entropy production).

**Theorem (sandwich bounds).** Assume the positive orthant is invariant and $x_t \to x_{\mathrm{eq}}$, the equilibrium in the stoichiometric class of $x_0$. Then $D_{\mathrm{KL}}(\cdot\|x_{\mathrm{eq}})$ satisfies a Polyak-Lojasiewicz inequality with constant $\underline\rho > 0$ and a Lipschitz-type upper inequality with constant $\overline\rho$ on the forward orbit of $x_0$, and for all $T \ge 0$

$$D_{\mathrm{KL}}(x_0\|x_{\mathrm{eq}})\, e^{-2\sigma_1^2\, \overline\rho\, \overline\Omega_T} \;\le\; D_{\mathrm{KL}}(x_T\|x_{\mathrm{eq}}) \;\le\; D_{\mathrm{KL}}(x_0\|x_{\mathrm{eq}})\, e^{-2\sigma_{\operatorname{rk}(S)}^2\, \underline\rho\, \underline\Omega_T},$$

where $\underline\Omega_T$ and $\overline\Omega_T$ are time integrals over $[0,T]$ of the minimum and maximum reaction activities $\min_r \omega_{\log,r}(x_t)$ and $\max_r \omega_{\log,r}(x_t)$, each weighted by the local convexity parameter of the divergence along the trajectory relative to $\underline\rho$, resp. $\overline\rho$.

The decay is therefore exponential in *integrated activity* rather than in time: plateaus and long transients (for example quasi-steady-state regimes with small activities) slow relaxation without breaking the bound. With the hyperbolic dissipation (geometric-mean activity and $\cosh$-type scalar dissipation) the exponentials are replaced by deformed exponentials.

## Depends on

- [Horn-Jackson inequality](../complex-balancing-and-the-deficiency-zero-theore/helmholtz-rate-nonpos.md)

## Expansion

The force lies in $\operatorname{im} S^\top$, so $\|f\|_2 \ge \sigma_{\operatorname{rk}(S)} \|\Pi\, \partial_x D_{\mathrm{KL}}\|_2$ for the projection $\Pi$ onto $(\ker S^\top)^\perp$, and $\|f\|_2 \le \sigma_1 \|\partial_x D\|_2$. The PL inequality turns the gradient norm into $D$ itself, and the entropy production of the quadratic dissipation is bounded below and above by the extreme activities times $\|f\|^2$. This gives a differential inequality $\dot D \le -2\sigma_{\operatorname{rk}}^2 \underline\rho\, \omega(x_t) D$ (and its reverse), which integrates by Gronwall to the stated bounds. Positivity of the PL and Lipschitz constants on the whole orbit follows from convergence to $x_{\mathrm{eq}}$ and strict convexity of the divergence.

## Sources

- Keisuke Sugie, Dimitri Loutchko, Tetsuya J. Kobayashi, "Convex Analysis of Relaxation Dynamics in Chemical Reaction Networks and Generalized Gradient Flows", arXiv:2602.18932 (2026), Lemma 3.1, Theorem 3.4, Theorem 3.5, Lemma 3.8 and Corollary 3.9, <https://doi.org/10.48550/arXiv.2602.18932>
