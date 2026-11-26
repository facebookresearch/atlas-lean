# Threshold dynamics of the diffusion time-changed SIS model

**Model.** In a closed population of size $N$ with transmission rate $\beta$, death/replacement rate $\mu$ and recovery rate $\gamma$, the number of infectives obeys

$$dI(t) = I(t)\big[\beta N - \mu - \gamma - \beta I(t)\big]\,dt + \sigma I(t)\big(N - I(t)\big)\,dB(E_t), \qquad I(0) = I_0 \in (0,N),$$

where $B$ is a standard Brownian motion and $E_t$ is the inverse of a subordinator $D$ (a non-decreasing Lévy process), $E_t = \inf\{u > 0 : D(u) > t\}$, independent of $B$. The drift runs in physical time while the noise runs on the random clock $E_t$, modelling environmental shocks that arrive with trapping (sub-diffusive) periods. Let $\mathcal R_0 = \beta N/(\mu + \gamma)$.

**Theorem.**
1. *Well-posedness.* For every $I_0 \in (0,N)$ there is a unique global solution with $P\{I(t) \in (0,N)\ \forall t \ge 0\} = 1$.
2. *Extinction.* If $\mathcal R_0 < 1$, then $\limsup_{t\to\infty} \tfrac1t \log I(t) < 0$ almost surely: the disease dies out exponentially fast.
3. *Persistence.* If $\mathcal R_0 > 1$, then almost surely $\limsup_{t\to\infty} I(t) \ge \xi$ and $\liminf_{t\to\infty} I(t) \le \xi$, where $\xi = N(1 - 1/\mathcal R_0)$ is the endemic equilibrium of the deterministic SIS model.
4. *Numerics.* If $E$ is the inverse of a standard $\alpha$-stable subordinator, $\alpha \in (0,1)$, a positivity-preserving logarithmic Euler–Maruyama scheme with step $\Delta$ satisfies $\max_k E|I_k - I(t_k)|^p \le C\Delta^{p\alpha}$ for each integer $p \ge 2$: strong order $\alpha$.

## Expansion

The threshold is the deterministic one, unlike the classical Brownian SIS model, where the noise shifts it by $\sigma^2N^2/2$. The reason is that for an $\alpha$-stable inverse subordinator $E_t/t \to 0$ almost surely: the random clock runs sublinearly, so in Itô's formula for $\log I(t)$ the Itô correction $-\tfrac12\sigma^2(N-I)^2\,dE_t$ and the martingale term $\int \sigma(N-I)\,dB(E_s)$ are both $o(t)$, and $\tfrac1t\log I(t)$ is governed by $\beta N - \mu - \gamma - \beta I$. For the numerical scheme, exponential moments $E[e^{\lambda E_t^r}] < \infty$ for $r < 1/(1-\rho)$ (with $\rho$ the regular-variation index of the Laplace exponent) control the local Lipschitz constants, and the bound $E[e^{cE_T}\sum_k (\Delta E_k)^{p+1}] \le C\Delta^{p\alpha}$ for the clock increments yields order $\alpha$.

## Sources

- Xiaotong Li, Huaqian Zhou and Ruchun Zuo, "A diffusion time-changed stochastic SIS epidemic model: well-posedness, long-time behavior, and numerical approximation", arXiv:2608.21930 (2026), well-posedness, extinction and persistence theorems, inverse-subordinator lemmas and the strong convergence theorem, <https://doi.org/10.48550/arXiv.2608.21930>.
