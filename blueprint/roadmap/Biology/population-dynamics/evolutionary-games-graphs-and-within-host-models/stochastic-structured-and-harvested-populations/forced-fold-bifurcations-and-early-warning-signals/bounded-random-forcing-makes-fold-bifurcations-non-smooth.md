# Bounded random forcing makes fold bifurcations non-smooth

In the [forced Allee model](lyapunov-gap-at-non-smooth-fold-bifurcations.md) $x' = \frac{r}{K^2}x(K-x)(x-S) - (\beta + \kappa F(t))x$ with $\kappa < b(r,K,S)(1-\gamma(K,S))$ and fold parameter $\beta_c \in J(r,K,S)$, let the forcing be the bounded random signal $F(t) = \tfrac{1+\sin(\theta_0 + W_t)}{2}$. For an invariant graph $\varphi$, the finite-time Lyapunov exponents over windows of length $T$ have maximum $\lambda_T^{\max}(\varphi)$ and minimum $\lambda_T^{\min}(\varphi)$ over the forcing states.

**Theorem.**

1. Every fold bifurcation of the randomly forced Allee model at a critical parameter $\beta_c \in J$ is non-smooth; consequently the Lyapunov exponent of the stable equilibrium does not tend to $0$ as $\beta \nearrow \beta_c$.
2. With random forcing, $\lim_{\beta\nearrow\beta_c} \lambda_T^{\max}(x^s_\beta) \ge 0$; more generally, for randomly forced monotone flows satisfying the reference-family hypotheses, the maximal finite-time exponents of the stable graph tend to $0$.
3. With quasiperiodic forcing and a non-smooth fold,

$$
\lim_{\beta\nearrow\beta_c} \lambda_T^{\max}(x^s_\beta) \ge \lambda(x^u_{\beta_c}) > 0, \qquad \lim_{\beta\nearrow\beta_c} \lambda_T^{\min}(x^u_\beta) \le \lambda(x^s_{\beta_c}) < 0 .
$$

## Depends on

- [Lyapunov gap at non-smooth fold bifurcations of a forced Allee model](lyapunov-gap-at-non-smooth-fold-bifurcations.md)

## Expansion

Bounded random forcing spends arbitrarily long stretches near any forcing value, in particular near the value at which the autonomous reference system $g_\beta$ already has its fold. On those stretches the randomly forced flow is close to the reference flow, so the two invariant graphs nearly touch on a set of positive measure while staying apart on average, which is the non-smooth scenario. Finite-time exponents, the quantity estimated from data, still detect the approach: their range widens up to the exponent of the other branch, so while asymptotic recovery rates give no warning, the spread of short-window recovery rates can.

## Sources

- Flavia Remo, Gabriel Fuhrmann and Tobias Jäger, *On the effect of forcing of fold bifurcations and early-warning signals in population dynamics*, arXiv:1904.06507, Theorems 2 and 3 (Section 1), Theorem 3.4 (Section 3) and Theorem 5.3 (Section 5). <https://doi.org/10.48550/arXiv.1904.06507> Published version: Nonlinearity 35 (2022) 6485–6527, <https://doi.org/10.1088/1361-6544/ac98ee>.
