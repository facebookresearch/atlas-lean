# Lévy subordinator limits of integrated reflected Wright–Fisher and Feller diffusions

**General principle.** Let $X_n$ be one-dimensional diffusions on intervals $I_n$ with normalized speed measures $m_n$ ($m_n(I_n) = 1$) and let $A_n(t) = \int_0^t \zeta_n(X_n(u))\,du$ be additive functionals. Under explicit conditions (the diffusions start from a law dominated by $m_n$, the hitting times of a reference point vanish, and the Laplace-exponent functions $\Phi_n(\mu)$ obtained from positive solutions of $\mathcal G_n\varphi = \mu\zeta_n\varphi$ converge), $A_n$ converges weakly in Skorokhod's $M_1$ topology to a Lévy subordinator whose Laplace exponent is $\Phi = \lim_n \Phi_n$.

**Theorem (Wright–Fisher).** Let $X_n$ be the Wright–Fisher diffusion on $[0,1)$ with generator

$$\mathcal G_n f(x) = \frac{1}{\tau_n}x(1-x)f''(x) + \frac{1}{\tau_n}\big(\alpha_n(1-x) - \beta x\big)f'(x),$$

started at $0$ and instantaneously reflected there, with $\beta > 1$ fixed, $\tau_n \to 0$ and $\alpha_n/\tau_n \to \gamma \in (0,\infty)$ (so the mutation rate into the boundary type vanishes and $0$ is a regular, reflecting boundary). Then

$$A_n(t) = \frac{1}{\tau_n}\int_0^t X_n(u)\,du$$

converges weakly to a Lévy subordinator with Laplace exponent

$$\Phi(\mu) = \gamma\sqrt\mu\,\frac{I_\beta(2\sqrt\mu)}{I_{\beta-1}(2\sqrt\mu)},$$

where $I_\nu$ is the modified Bessel function of the first kind.

**Theorem (Feller).** Let $X_n$ be the Feller (CIR) diffusion on $[0,\infty)$ with generator $\mathcal G_n f = nxf'' + n(\alpha_n - \beta x)f'$, started at $0$ and reflected there, with $\beta > 0$, $\alpha_n < 1$ and $n\alpha_n \to \gamma > 0$. Then $A_n(t) = n\int_0^t X_n(u)\,du$ converges weakly to the subordinator with

$$\Phi(\mu) = \frac{\gamma\beta}{2}\Big(\sqrt{1 + \frac{4\mu}{\beta^2}} - 1\Big),$$

the inverse-Gaussian subordinator with mean $\gamma/\beta$ per unit time.

## Expansion

In these regimes the diffusion spends almost all its time near $0$ and makes rare, fast excursions away from it; integrating $X_n$ turns each excursion into a jump of $A_n$, so the limit is a pure-jump increasing Lévy process. Its Laplace exponent is computed from the eigenfunction problem $\mathcal G_n\varphi = \mu x\varphi$: for Wright–Fisher, the solutions are confluent hypergeometric functions whose limit gives the Bessel ratio, and for Feller, Kummer's $U$-function gives the inverse-Gaussian exponent. Such subordinators model the cumulative synchrony input in doubly stochastic models of spiking activity, where a reflected diffusion parametrizes instantaneous correlations among neurons.

## Sources

- T. Taillefumier, G. Žitković, "A functional limit theorem for additive functionals", arXiv:2410.06383 (2024), Theorems 2.1 and 2.4 (Section 2), Theorems 3.3–3.4 and Remark 3.5 (Section 3), <https://doi.org/10.48550/arXiv.2410.06383>.
