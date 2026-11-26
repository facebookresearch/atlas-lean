# Threshold of the degree-based SIR model with distributed infectivity delay

**Model.** On an uncorrelated contact network with degree distribution $P(k)$, $k = 1, \dots, n$, mean degree $\langle k\rangle = \sum_k kP(k)$ and second moment $\langle k^2\rangle = \sum_k k^2 P(k)$, let $S_k(t)$, $I_k(t)$, $R_k(t)$ be the susceptible, infected and removed fractions of degree-$k$ nodes, $S_k + I_k + R_k = 1$. Put $a_k = kP(k)/\langle k\rangle$ and let

$$\theta(t) = \sum_{k=1}^n a_k I_k(t)$$

be the probability that a random edge points to an infected node. Infectiousness varies with time since infection through a kernel $f \ge 0$ on $[0, \infty)$ with $\int_0^\infty f < \infty$. With birth and death rate $\mu > 0$, transmission rate $\beta > 0$ and removal rate $\gamma > 0$,

$$\dot S_k = \mu - \mu S_k - \beta k S_k \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, \theta(t-\tau)\, d\tau, \qquad \dot I_k = \beta k S_k \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, \theta(t-\tau)\, d\tau - (\mu + \gamma) I_k,$$

for $k = 1, \dots, n$, where $e^{-(\mu+\gamma)\tau}$ is the probability of remaining alive and infectious for time $\tau$. Let

$$\hat f = \int_0^\infty f(\tau) e^{-(\mu+\gamma)\tau}\, d\tau, \qquad \mathcal R_0 = \frac{\beta\, \hat f}{\mu + \gamma}\, \frac{\langle k^2\rangle}{\langle k\rangle}.$$

**Theorem.**

1. The disease-free equilibrium $E_0$ ($S_k = 1$, $I_k = 0$) always exists. If $\mathcal R_0 \le 1$ there is no endemic equilibrium. If $\mathcal R_0 > 1$ there is a unique endemic equilibrium $E_+$, with

$$S_k^* = \frac{\mu}{\beta k \hat f \theta^* + \mu}, \qquad I_k^* = \frac{\mu\, \beta k \hat f \theta^*}{(\mu + \gamma)(\beta k \hat f \theta^* + \mu)},$$

where $\theta^*$ is the unique positive root of $g(x) = x$ with $g(x) = \frac{\mu}{\mu+\gamma}\sum_k a_k \frac{\beta k \hat f x}{\beta k \hat f x + \mu}$.
2. $E_0$ is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.
3. $I_k^*$ increases with the degree $k$: better-connected nodes carry higher endemic prevalence.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At equilibrium the delay integral equals $\hat f\,\theta^*$, which gives the formulas for $S_k^*, I_k^*$; substituting them into $\theta^* = \sum_k a_k I_k^*$ gives $\theta^* = g(\theta^*)$. The function $g$ is increasing and strictly concave on $[0, \infty)$ with $g(0) = 0$, $g(1) < 1$ and $g'(0) = \frac{\beta \hat f}{\mu+\gamma}\sum_k k a_k = \mathcal R_0$, so a positive fixed point exists, and is unique, exactly when $\mathcal R_0 > 1$. For local stability at $E_0$, the linearization has $n$ eigenvalues $-\mu$, $n - 1$ eigenvalues $-(\mu+\gamma)$, and one more root $\Lambda$ of

$$\Lambda + \mu + \gamma = \beta \frac{\langle k^2\rangle}{\langle k\rangle} \int_0^\infty f(\tau) e^{-(\Lambda + \mu+\gamma)\tau}\, d\tau .$$

The real function $\varphi(x) = x - (\mu+\gamma)\bigl[\mathcal R_0 \hat f^{-1}\int_0^\infty f e^{-(x+\mu+\gamma)\tau}\,d\tau - 1\bigr]$ is increasing with $\varphi(0) = -(\mu+\gamma)(\mathcal R_0 - 1)$, so there is a positive real root iff $\mathcal R_0 > 1$; when $\mathcal R_0 < 1$, a root with nonnegative real part is impossible because the right side then has real part below $\mu + \gamma$. The threshold grows with the network heterogeneity $\langle k^2\rangle/\langle k\rangle$ and with the delay kernel; $f = \delta_{\tau_0}$ recovers a discrete delay.

## Sources

- C. Huang, J. Cao, F. Wen, X. Yang, "Stability Analysis of SIR Model with Distributed Delay on Complex Networks", *PLoS ONE* 11(8) (2016) e0158813, model (3), Eq. (6), Theorems 1–2, Remark 5. <https://doi.org/10.1371/journal.pone.0158813> (PMC4973911).
