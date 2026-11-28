# Linear stability of a uniform self-propelled particle density among obstacles

Consider the one-dimensional SPP–obstacle macromodel on $\mathbb{R}$ (case a) or on $[0,1]$ with periodic boundary conditions (case b). Linearize around a constant SPP density $\rho_0 > 0$, with the obstacle density expanded to second order in $\gamma$. A mode $\rho_g = \rho\, e^{ikx + \alpha t}$ has growth rate

$$
\alpha(k) = \frac{-ik c_1 + \tfrac{\rho_0}{\zeta} k^2\Big(\tfrac{\gamma}{\eta\delta}\big(1 - e^{-\delta k^2}\big)\hat\phi_k^2 - \mu\Big)}{1 + D(k)},
\qquad \hat\phi_k = \int e^{-ikx}\phi(x)\,dx ,
$$

where $D(k) \ge 0$ comes from the order-$\gamma^2$ memory term $-\tfrac{\gamma^2}{\eta}\partial_t\partial_x^2\bar\rho_g$ of the obstacle density, and $D \equiv 0$ at first order in $\gamma$.

**Proposition 1(ii).** The uniform state is linearly stable iff

$$
\max_{k \in K} \frac{1}{\delta}\big(1 - e^{-\delta k^2}\big)\hat\phi_k^2 < \frac{\mu\eta}{\gamma},
$$

where $K = \mathbb{R}$ (case a) or $K = 2\pi\mathbb{Z}$ (case b). Because $\delta^{-1}(1 - e^{-\delta k^2}) \le k^2$, obstacle noise is stabilizing. In the noiseless limit (Corollary 2), $\operatorname{Re}\alpha(k) = \tfrac{\rho_0 k^2}{\zeta}\big(\tfrac{\gamma}{\eta}(k\hat\phi_k)^2 - \mu\big)$ at first order in $\gamma$. The condition becomes $\max_k (k\hat\phi_k)^2 < \mu\eta/\gamma$. Self-repulsion $\mu$, stiff springs (small $\gamma = \eta/\kappa$) and high obstacle friction all stabilize.

**Example (compactly supported linear force).** For $\phi(x) = \tfrac{3C}{2r_I}(1 - |x|/r_I)^2$ on $|x| < r_I$, and $\phi = 0$ otherwise,

$$
\hat\phi_k = 6C\, \frac{r_I k - \sin(r_I k)}{(r_I k)^3},
$$

and $(k\hat\phi_k)^2$ is maximized at $k = \pi/r_I$. So the uniform state is linearly stable whenever $\big(6C/(\pi r_I)\big)^2 < \mu\eta/\gamma$. When it is unstable, the most unstable mode $k = 2\pi l_{\max}$ predicts a pattern size of about $1/l_{\max}$.

## Depends on

- [Quasi-static obstacle density under strong tethers](quasi-static-obstacle-density-under-strong-tethers.md)

## Expansion

Fourier transform the linearized equation $\partial_t\rho_g + c_1\partial_x\rho_g = \tfrac{\rho_0}{\zeta}\partial_x^2(\mu\rho_g + \phi * \rho_f)$, using $\widehat{M_{2\delta}} = e^{-\delta k^2}$. Substituting the second-order obstacle density, whose $\partial_t$ term moves to the left-hand side and produces the factor $1 + D(k)$, gives $\partial_t\hat\rho_g = \alpha(k)\hat\rho_g$. The denominator is positive, so stability is decided by the real part of the numerator. The order-$\gamma^2$ correction changes growth and decay rates but not the stability threshold. For purely local interactions, $\hat\phi_k$ is constant, and every parameter set is unstable at high frequencies. The non-locality of the SPP–obstacle interaction is therefore what selects a finite pattern wavelength. Direct simulations of both the macromodel and the individual-based model match the predicted number of peaks as $r_I$ varies.

## Sources

- Aceves-Sanchez P, Degond P, Keaveny EE, Manhart A, Merino-Aceituno S, Peurichard D. Large-scale dynamics of self-propelled particles moving through obstacles: model derivation and pattern formation. *Bulletin of Mathematical Biology* 82 (2020) 129. <https://doi.org/10.1007/s11538-020-00805-z>. PMCID: PMC7519010.
