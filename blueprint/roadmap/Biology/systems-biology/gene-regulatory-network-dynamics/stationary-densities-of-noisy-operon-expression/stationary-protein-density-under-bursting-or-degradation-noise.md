# Stationary protein density of an operon under transcriptional bursting or degradation noise

**Model.** In a population of cells, let $x \ge 0$ be the (dimensionless) level of the slow effector of an operon, degraded at rate $\gamma$ and produced with a regulated rate $\gamma\kappa f(x)$, where for an inducible operon $f(x) = \dfrac{1 + x^n}{K + x^n}$ with $K > 1$ and Hill coefficient $n$ (a repressible operon uses a decreasing $f$).
- *Bursting:* production occurs in bursts at rate $\gamma\kappa_b f(x)$ with exponentially distributed amplitudes $h(y) = b^{-1}e^{-y/b}$ (mean burst size $b$). The density $u(t,x)$ of $x$ across cells obeys

$$\partial_t u - \gamma\,\partial_x(xu) = -\gamma\kappa_b f(x)u + \gamma\kappa_b\int_0^x f(y)u(t,y)h(x-y)\,dy.$$

- *Degradation noise:* $dx = \gamma\big[\kappa_d f(x) - x\big]dt + \sigma\sqrt{x}\,dw$ (Itô), with Fokker–Planck equation $\partial_t u = -\partial_x\big[(\gamma\kappa_d f - \gamma x)u\big] + \frac{\sigma^2}{2}\partial_x^2(xu)$ and a reflecting boundary at $0$.

**Theorem.**
1. With bursting, the equation has the unique stationary density

$$u_*(x) = \frac{\mathcal{C}}{x}\,e^{-x/b}\exp\Big[\kappa_b\int^x \frac{f(y)}{y}\,dy\Big],$$

with $\mathcal{C}$ a normalizing constant, and every solution converges to it in $L^1$ (asymptotic stability). For the inducible operon this is

$$u_*(x) = \mathcal{C}\,e^{-x/b}\,x^{\kappa_b/K - 1}\,(K + x^n)^{\theta}, \qquad \theta = \frac{\kappa_b}{n}\Big(1 - \frac1K\Big),$$

whose interior critical points solve $\frac{1}{\kappa_b}\big(\frac{x}{b} + 1\big) = \frac{1 + x^n}{K + x^n}$. Let $x_\pm$ be the positive roots of the tangency equation $x^{2n} - (K-1)\big[n - \frac{K+1}{K-1}\big]x^n - nb(K-1)x^{n-1} + K = 0$ and $\kappa_{b\pm} = \frac{x_\mp + b}{b}\cdot\frac{K + x_\mp^n}{1 + x_\mp^n}$. Then $u_*$ is bimodal of type 1 ($u_*(0) = \infty$ and a single interior maximum) for $\kappa_{b-} < \kappa_b < K$, and bimodal of type 2 ($u_*(0) = 0$ and two interior maxima $0 < \tilde x_1 < \tilde x_3$) for $\kappa_{b-} < \kappa_b < \kappa_{b+}$ and $K < \kappa_b$ (for $n = 4$, $K = 10$, $b = 1$: $\kappa_{b-} \approx 4.29$, $\kappa_{b+} \approx 14.35$). This is the stochastic counterpart of deterministic bistability.
2. With degradation noise, the unique, asymptotically stable stationary density is

$$u_*(x) = \frac{\mathcal{C}}{x}\,e^{-2\gamma x/\sigma^2}\exp\Big[\kappa_e\int^x \frac{f(y)}{y}\,dy\Big], \qquad \kappa_e = \frac{2\gamma\kappa_d}{\sigma^2}.$$

Consequently the two noise sources give identical stationary densities under $b \leftrightarrow \sigma^2/(2\gamma)$ and $\kappa_b \leftrightarrow \kappa_e$: bursting and degradation noise cannot be distinguished from stationary distributions when each acts alone, and their bimodality regions coincide.

## Proof sketch

Writing $y = xu_*$, the stationary bursting equation becomes, after a Laplace transform in $x$, the first-order ODE $y' + y/b - \kappa_b f(x)y/x = 0$, solved by quadrature; uniqueness and convergence follow from the theory of stochastic semigroups for this piecewise-deterministic Markov process. For the diffusion, zero probability flux at the reflecting boundary gives the stationary density directly. In both cases the density is a Gamma-like factor times $\exp(\kappa\int f/y)$; the exponential tail rate is $1/b$ for bursts and $2\gamma/\sigma^2$ for degradation noise, which is why the two models are interchangeable at the level of distributions. Letting the noise vanish ($b \to 0$ with $b\kappa_b$ fixed, or $\sigma \to 0$) concentrates $u_*$ on the stable steady states of the deterministic operon model.

## Sources

- Michael C. Mackey, Marta Tyran-Kamińska and Romain Yvinec, "Molecular distributions in gene regulatory dynamics", *Journal of Theoretical Biology* 274 (2011), 84–96, <https://doi.org/10.1016/j.jtbi.2011.01.020>. Preprint version: arXiv:1009.5810 (2010), Section 2 (operon model, Theorems 1 and 2 quoted from earlier work), Section 4 (bursting: Theorem 3 and the inducible-operon bimodality analysis, with the tangency equation for $x_\pm$, the formula for $\kappa_{b\pm}$ and the unimodal and bimodal types), Section 5 (degradation noise: Theorem 4), <https://doi.org/10.48550/arXiv.1009.5810>.
