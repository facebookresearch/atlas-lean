# SPDE for fluctuations of the infection-age measure in a varying-infectivity SIR epidemic

**Setting.** In the varying-infectivity SIR model with infection-age measure $\mu^N_t$ and law-of-large-numbers limit $\bar\mu_t$, define the fluctuation process $\hat\mu^N_t(\varphi) = \sqrt N\big(\bar\mu^N_t(\varphi) - \bar\mu_t(\varphi)\big)$. Define $\hat X^N = \sqrt N(\bar X^N - \bar X)$ in the same way for the other epidemic processes, in particular the infection rate $\Upsilon^N$. Let $W_{\mathrm{inf}}$ be a standard Gaussian white noise on $\mathbb R_+$ and $W_{\mathrm{rec}}$ an independent centered Gaussian white noise on $\mathbb R_+^2$ with

$$\mathbb E\Big[\Big(\int_0^\infty\!\!\int_0^\infty g(s,\mathfrak a)\,W_{\mathrm{rec}}(ds, d\mathfrak a)\Big)^2\Big] = \int_0^\infty\!\!\int_0^\infty g^2(s, \mathfrak a)\,h(\mathfrak a)\,\bar\mu_s(d\mathfrak a)\,ds .$$

These are the infection and recovery noises. Let $\hat\mu_0$ be the Gaussian limit of the initial fluctuations.

**Theorem (functional central limit theorem).** Assume the initial-age conditions of the law of large numbers, $F \in C^1$ and $F(\mathfrak a) > 0$ for all $\mathfrak a > 0$, and $\hat\Upsilon^N \Rightarrow \hat\Upsilon$ in $D$. Then

$$\{\hat\mu^N_t\}_{t\ge0} \Rightarrow \{\hat\mu_t\}_{t\ge0} \quad \text{in } D\big(\mathbb R_+, (H^1(\mathbb R_+))'\big),$$

with $\hat\mu \in C\big(\mathbb R_+, (H^1(\mathbb R_+))'\big)$ almost surely given, for $\varphi \in H^1(\mathbb R_+)$, by

$$\hat\mu_t(\varphi) = \int_0^\infty \varphi(t+\mathfrak a)\frac{F^c(t+\mathfrak a)}{F^c(\mathfrak a)}\,\hat\mu_0(d\mathfrak a) + \int_0^t \varphi(t-\mathfrak a)F^c(t-\mathfrak a)\Big[\hat\Upsilon(\mathfrak a)\,d\mathfrak a + \sqrt{\bar\Upsilon(\mathfrak a)}\,W_{\mathrm{inf}}(d\mathfrak a)\Big] + \int_0^t\!\!\int_0^\infty \varphi(t-s+\mathfrak a)\frac{F^c(t-s+\mathfrak a)}{F^c(\mathfrak a)}\,W_{\mathrm{rec}}(ds, d\mathfrak a).$$

If moreover $F$ has locally bounded derivatives $f$ and $f'$, this $\hat\mu$ is the unique solution in that space of the linear SPDE, for $\varphi \in H^2_c(\mathbb R_+)$,

$$\hat\mu_t(\varphi) = \hat\mu_0(\varphi) + \int_0^t \hat\mu_s(\varphi' - h\varphi)\,ds + \varphi(0)\int_0^t\Big[\hat\Upsilon_s\,ds + \sqrt{\bar\Upsilon(s)}\,W_{\mathrm{inf}}(ds)\Big] + \int_0^t\!\!\int_0^\infty \varphi(\mathfrak a)\,W_{\mathrm{rec}}(ds, d\mathfrak a).$$

Informally, $\partial_t\hat\mu + \partial_{\mathfrak a}\hat\mu = -h\hat\mu + \partial^2_{t\mathfrak a}W_{\mathrm{rec}}$, with boundary value $\hat\mu(t, 0) = \hat\Upsilon(t) + \sqrt{\bar\Upsilon(t)}\,\dot W_{\mathrm{inf}}(t)$. The limit $\hat\Upsilon$ solves a system of stochastic Volterra-type linear integral equations driven by three independent Gaussian noises: $W_{\mathrm{inf}}$, $W_{\mathrm{rec}}$, and a noise from the random infectivity functions.

## Depends on

- [PDE limit of the infection-age measure in a varying-infectivity SIR epidemic](pde-limit-of-the-infection-age-measure-in-varying-infectivity-sir.md)

## Expansion

The fluctuation equation is the same transport-with-killing PDE as the deterministic limit, now with random inputs. New infections enter at age $0$ with the linearized rate $\hat\Upsilon$ plus Poisson noise of variance $\bar\Upsilon$, and recoveries add white noise whose intensity is the recovery flux $h\,\bar\mu$. The explicit solution is the same characteristic formula as in the deterministic case, applied to the Gaussian inputs $(\hat\mu_0, \hat\Upsilon, W_{\mathrm{inf}}, W_{\mathrm{rec}})$. These inputs are jointly Gaussian, and $\hat\mu_0, W_{\mathrm{inf}}, W_{\mathrm{rec}}$ are mutually independent. Tightness is proved in the dual Sobolev space $(H^1)'$. Uniqueness of the SPDE solution is proved only under the stronger smoothness assumption on $F$.

## Sources

- Guodong Pang and Etienne Pardoux, "SPDE for stochastic SIR epidemic models with infection-age dependent infectivity", Stochastics and Partial Differential Equations: Analysis and Computations 14 (2025), 776–829, <https://doi.org/10.1007/s40072-025-00403-x>; numbering as in arXiv:2410.17200: Section 2.4, Proposition 2.1, Theorem 2.2, Theorem 2.3.
