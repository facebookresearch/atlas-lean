# Threshold dynamics of a latency- and relapse-age tuberculosis model

**Model.** Let $S(t), I(t), T(t)$ be the susceptible, infectious and under-treatment populations, $e(t,a)$ the density of latently infected individuals with latency age $a$, and $r(t,\theta)$ the density of recovered individuals with relapse age $\theta$:

$$\begin{aligned}
S' &= \Lambda - \beta S (I + \rho T) - \mu S,\\
I' &= \int_0^\infty \sigma(a) e(t,a)\,da + \int_0^\infty \omega(\theta) r(t,\theta)\,d\theta + (1-\eta)\rho_1 T - (\gamma + \mu + \mu_I) I,\\
T' &= \gamma I - (\mu + \mu_T + \alpha + \rho_1) T,\\
(\partial_t + \partial_a) e &= -(\mu + \delta(a) + \sigma(a)) e, \qquad (\partial_t + \partial_\theta) r = -(\mu + \omega(\theta)) r,
\end{aligned}$$

with boundary conditions $e(t,0) = \beta S (I + \rho T) + \eta \rho_1 T$ and $r(t,0) = \int_0^\infty \delta(a) e(t,a)\,da + \alpha T$. Assume all constants are positive, $0 < \eta < 1$, and $\sigma, \delta, \omega \in L^\infty_+(0,\infty)$. Here $\sigma(a)$ is age-dependent progression to active disease, $\delta(a)$ treatment of latent infection, $\omega(\theta)$ age-dependent relapse, $\rho$ the relative infectiousness of treated individuals, and $\rho_1$ reinfection during treatment, a fraction $\eta$ of which enters latency. The phase space is $Y = \mathbb{R}_+^3 \times L^1_+(0,\infty)^2$.

Write $k_1(a) = e^{-\int_0^a (\mu + \delta + \sigma)}$, $k_2(\theta) = e^{-\int_0^\theta (\mu + \omega)}$, $K_1 = \int_0^\infty \sigma k_1$, $K_2 = \int_0^\infty \omega k_2$, $K_3 = \int_0^\infty \delta k_1$, $D_I = \gamma + \mu + \mu_I$, $D_T = \mu + \mu_T + \alpha + \rho_1$, and

$$\mathcal{R}_0 = \frac{\beta (K_1 + K_2 K_3)}{D_I}\frac{\Lambda}{\mu} + \frac{\gamma\big(\alpha K_2 + (1-\eta)\rho_1 + (\beta \rho \Lambda/\mu + \eta \rho_1)(K_1 + K_2 K_3)\big)}{D_I D_T}.$$

**Theorem.**
1. The system generates a continuous, point-dissipative, asymptotically smooth semiflow on $Y$ with a global attractor; the set $\{\|x\|_Y \le \Lambda/\mu\}$ is positively invariant.
2. The disease-free equilibrium $E_0 = (\Lambda/\mu, 0, 0, 0, 0)$ always exists and is globally asymptotically stable if $\mathcal{R}_0 < 1$.
3. If $\mathcal{R}_0 > 1$ there is a unique endemic equilibrium $E^*$. If moreover $\sigma$, $\delta$ and $\omega$ are not eventually zero (none vanishes almost everywhere on a half-line $(A, \infty)$), the semiflow is uniformly persistent and $E^*$ is globally asymptotically stable on the set of states with some infection present.

## Expansion

Linearizing at an equilibrium and seeking exponential solutions reduces stability to the characteristic equation $f(\lambda) = 1$, with $f$ built from the Laplace transforms $k_1(\lambda) = \int \sigma(a) e^{-\int_0^a (\lambda + \mu + \sigma + \delta)}da$, $k_2(\lambda)$ and $k_3(\lambda)$ of the latency and relapse kernels; at $E_0$, $f(0) = \mathcal{R}_0$, which gives local stability for $\mathcal{R}_0 < 1$ and a positive real root for $\mathcal{R}_0 > 1$. Each term of $\mathcal{R}_0$ counts a route back to active disease: direct progression from latency ($K_1$), latency followed by treatment and relapse ($K_2 K_3$), infection by treated cases ($\rho$), reinfection during treatment ($\rho_1$, split by $\eta$), and relapse after completed treatment ($\alpha K_2$). Asymptotic smoothness follows by splitting the semiflow into a part with compact closure and a part decaying to zero; global stability uses Volterra-type Lyapunov functionals built from $g(x) = x - \ln x - 1$ with age-weighted integrals over $e$ and $r$, and persistence uses the Hale–Waltman theorem.

## Depends on

- [Spectral bound and reproduction number for infinite-dimensional structure](../../next-generation-matrix-and-the-basic-reproductio/spectral-bound-and-reproduction-number-for-infinite-dimensional-structure.md)

## Sources

- Z.-K. Guo, H. Xiang, H.-F. Huo, "Analysis of an age-structured tuberculosis model with treatment and relapse", Journal of Mathematical Biology 82(5) (2021) 45, model (1)–(2), reproduction number (7), Propositions 1–3 and Theorems 1–8, <https://doi.org/10.1007/s00285-021-01595-1>, PMCID PMC8018515.
