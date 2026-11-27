# Interspike interval statistics of the stochastic FitzHugh–Nagumo model

**Model.** The stochastic FitzHugh–Nagumo equations for membrane potential $x$ and recovery variable $y$ are

$$dx_t = \frac{1}{\varepsilon}(x_t - x_t^3 + y_t)\,dt + \frac{\sigma_1}{\sqrt\varepsilon}\,dW^{(1)}_t, \qquad dy_t = (a - x_t - cy_t)\,dt + \sigma_2\,dW^{(2)}_t,$$

with time-scale separation $\varepsilon \ll 1$, independent Wiener processes and $\sigma_1, \sigma_2 > 0$. Let $\alpha_* = \sqrt{(1 - c\varepsilon)/3}$ and $\delta = a - \alpha_* - c(\alpha_*^3 - \alpha_*)$, small and positive in the excitable regime, where the deterministic system has a stable focus (quiescence) near a fold and spikes are large excursions. Between consecutive spikes the system performs small-amplitude oscillations (SAOs) around the focus, a mixed-mode pattern. Fix a curve $\mathcal{F}$ transverse to the oscillations; successive crossings define a substochastic Markov kernel $K$ on $\mathcal{F}$ (the process is killed when it spikes instead of completing an SAO), and $N$ is the number of SAOs between two spikes.

**Theorem.**
1. *(Asymptotically geometric SAO count.)* For any initial distribution $\mu_0$ on $\mathcal{F}$: $K$ has a quasi-stationary distribution $\pi_0$ with principal eigenvalue $\lambda_0 = \lambda_0(\varepsilon, a, c, \sigma_1, \sigma_2) < 1$; $N$ is almost surely finite; and

$$\lim_{n\to\infty}\mathbb{P}_{\mu_0}(N = n + 1 \mid N > n) = 1 - \lambda_0,$$

with $\mathbb{E}_{\mu_0}[r^N] < \infty$ for $r < 1/\lambda_0$, so all moments of $N$ are finite.
2. *(Weak-noise regime.)* If $\varepsilon$ and $\delta/\sqrt\varepsilon$ are small (and $\delta \ge |c|\varepsilon^{\beta}$ for some $\beta < 1$ when $c \ne 0$), there is $\kappa > 0$ such that whenever $\sigma_1^2 + \sigma_2^2 \le (\varepsilon^{1/4}\delta)^2/\log(\sqrt\varepsilon/\delta)$,

$$1 - \lambda_0 \le \exp\Big\{-\kappa\,\frac{(\varepsilon^{1/4}\delta)^2}{\sigma_1^2 + \sigma_2^2}\Big\}, \qquad \mathbb{E}_{\mu_0}[N] \ge C(\mu_0)\exp\Big\{\kappa\,\frac{(\varepsilon^{1/4}\delta)^2}{\sigma_1^2+\sigma_2^2}\Big\},$$

where $C(\mu_0)$ is the probability that the incoming path lands above the separatrix: spikes are exponentially rare.
3. *(Weak-to-strong transition.)* In rescaled variables with $\tilde\mu = 3\alpha_*(\delta - 3\alpha_*\sigma_1^2/\varepsilon)/\sqrt\varepsilon$ and $\tilde\sigma^2 = 9\alpha_*^2\varepsilon^{-3/2}(\sigma_1^2 + \sigma_2^2)$, the probability that one SAO escapes past the separatrix is

$$\Phi\big(-\pi^{1/4}\,\tilde\mu/\tilde\sigma\,[1 + o(1)]\big),$$

with $\Phi$ the standard normal distribution function, so the spiking probability per oscillation is governed by the single ratio $\varepsilon^{1/4}(\delta - 3\alpha_*\sigma_1^2/\varepsilon)/\sqrt{\sigma_1^2 + \sigma_2^2}$.

## Expansion

Near the fold the dynamics reduces to a canonical slow–fast system in which a spike occurs when noise pushes a trajectory across the separatrix during one rotation. Each rotation is a Markov step with a small escape probability, so the SAO count is the killing time of a substochastic chain, and Perron–Frobenius theory for positive kernels makes it asymptotically geometric with parameter $1 - \lambda_0$. The escape probability per turn is Gaussian in the distance to the separatrix divided by the noise accumulated over one turn, giving large-deviation behavior for weak noise and the normal-tail formula in the transition regime. Interspike intervals of excitable neurons are therefore long sequences of subthreshold oscillations with nearly exponential length statistics.

## Sources

- Nils Berglund and Damien Landon, "Mixed-mode oscillations and interspike interval statistics in the stochastic FitzHugh–Nagumo model", Nonlinearity 25 (2012), 2303–2335, <https://doi.org/10.1088/0951-7715/25/8/2303>; numbering as in arXiv:1105.1278: Section 2 (model, equations for $\alpha_*$ and $\delta$), Theorem on general properties of $N$ (Section 3), weak-noise Theorem (Section 4) and the transition Proposition (Section 5).
