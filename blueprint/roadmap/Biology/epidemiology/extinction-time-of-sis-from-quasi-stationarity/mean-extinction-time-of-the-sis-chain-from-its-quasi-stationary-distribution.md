# Mean extinction time of the stochastic SIS chain from its quasi-stationary distribution

**Model.** In a closed population of size $n$ with no demography, the number of infected $Y_n(t) \in \{0, 1, \dots, n\}$ is a birth-death chain with infection rate $\lambda i (n-i)/n$ and recovery rate $\gamma i$ from state $i$; state $0$ is absorbing and $R_0 = \lambda/\gamma$. Let $Q_{TT}$ be the generator restricted to the transient states $\{1, \dots, n\}$, and $\tilde{\mathbf q} = (\tilde q_1, \dots, \tilde q_n)$ the quasi-stationary distribution: the normalized left eigenvector of $Q_{TT}$ for its eigenvalue $\lambda_1 < 0$ of largest real part, i.e. the limiting law of $Y_n(t)$ conditioned on non-extinction.

**Result (Section 3).** Started from the quasi-stationary distribution, the extinction time $T_Q$ satisfies $\Pr(T_Q > t) = \tilde{\mathbf q}\, e^{Q_{TT} t} \mathbf{1} = e^{\lambda_1 t}$, so $T_Q$ is exponentially distributed, and since only state $1$ leaks to $0$ (at rate $\gamma$),

$$ \lambda_1 = -\gamma \tilde q_1, \qquad \mathbb{E}[T_Q] = \frac{1}{\gamma\, \tilde q_1}. $$

**Normal approximation (Section 4).** For $R_0 > 1$ the diffusion (Ethier-Kurtz) central limit theorem around the endemic level $1 - R_0^{-1}$ gives $\sqrt{n}\bigl(Y_n(t)/n - (1 - R_0^{-1})\bigr) \Rightarrow N(0, \sigma^2(t))$ with $\frac{d\sigma^2}{dt} = 2\frac{\gamma}{\lambda}(\lambda - \gamma) - 2(\lambda - \gamma)\sigma^2$, so $\sigma^2(t) \to R_0^{-1}$. Approximating the quasi-stationary distribution by $N(\mu_n, \sigma_n^2)$ with $\mu_n = (1 - R_0^{-1}) n$, $\sigma_n^2 = n/R_0$, conditioned to $[\tfrac12, n + \tfrac12]$ with a continuity correction, gives

$$ \mathbb{E}[T_Q] \approx \frac{\sigma_n}{\gamma\, \phi\bigl( \frac{1 - \mu_n}{\sigma_n} \bigr)} \Bigl[ \Phi\Bigl( \frac{n + \frac12 - \mu_n}{\sigma_n} \Bigr) - \Phi\Bigl( \frac{\frac12 - \mu_n}{\sigma_n} \Bigr) \Bigr], $$

with $\phi, \Phi$ the standard normal density and distribution function. Since $(1 - \mu_n)/\sigma_n \approx -\sqrt{n R_0}\,(1 - R_0^{-1})$, this exhibits the exponential growth of the endemic persistence time in $n$, of order $e^{n (R_0 - 1)^2/(2R_0)}$ up to polynomial factors, within the normal approximation (which is known to be inaccurate in the far tail near $0$).

## Expansion

Because $\tilde{\mathbf q}$ is a left eigenvector, $\tilde{\mathbf q} e^{Q_{TT} t} = e^{\lambda_1 t} \tilde{\mathbf q}$, and summing coordinates gives the survival function. Multiplying the eigen-equation $\tilde{\mathbf q} Q_{TT} = \lambda_1 \tilde{\mathbf q}$ on the right by $\mathbf{1}$, and using that the row sums of $Q_{TT}$ vanish except in state $1$, where the row sum is $-\gamma$ (the rate of recovery into the absorbing state), yields $-\gamma \tilde q_1 = \lambda_1$. The diffusion approximation linearizes the drift $F(y) = \lambda y(1-y) - \gamma y$ at $\hat y = 1 - R_0^{-1}$, where $F'(\hat y) = -(\lambda - \gamma)$, with infinitesimal variance $G(\hat y) = 2\frac{\gamma}{\lambda}(\lambda - \gamma)$, which gives the variance equation; evaluating the approximate density at state $1$ estimates $\tilde q_1$.

## Sources

- Kurnia Susvitasari, "Expected Time to Extinction of SIS Epidemic Model Using Quasy Stationary Distribution", arXiv (2018). Section 2 (birth-death formulation), Section 3 (quasi-stationary extinction time), Section 4 (Ethier-Kurtz central limit theorem and the normal approximation of the mean extinction time). <https://doi.org/10.48550/arXiv.1803.06096>
