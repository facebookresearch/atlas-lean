# Wald's inequality on the acceptance of the null hypothesis

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. For all $a, b \in \mathbb{R}$, the [SPRT](sprt-time.md) with log-boundaries $a$ and $b$ and stopping time $N$ satisfies

$$P_1^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \le a) \le e^a\, P_0^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \le a),$$

both events requiring the test to stop. This is the first line of Wald's inequalities, $\beta = \int_{\lambda_N \le A} \lambda_N \, dP_0 \le A (1 - \alpha)$ (Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2), whose lower boundary $A$ is $e^a$ in the notation above); $1 - \alpha$ equals $P_0(\text{accept } P_0)$ when the SPRT stops $P_0$-almost surely. The source takes $a < 0 < b$; the inequality holds for all $a$ and $b$.

The proof splits the event according to the value $n$ of the stopping time. On $\{N = n,\ \Lambda_n \le a\}$, an event of the first $n$ observations, the likelihood-ratio change of measure gives $P_1 = \int R_n \, dP_0$ with $R_n = e^{\Lambda_n} \le e^a$; summing over $n$ gives the inequality.

## Sources

- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3), first line of (a2).

## Informally uses

- [Likelihood-ratio change of measure on the first $n$ observations](infinite-pi-apply-eq-set-lintegral-prod.md)
- [The SPRT stopping time is a stopping time](is-stopping-time-sprt-time.md)

## Background

- [Wald's equation](../../martingales/wald-s-equations/wald-equation.md): combined with these inequalities (ignoring overshoot) it gives Wald's approximations (a3) to the average sample numbers $\mathsf E_0 N$ and $\mathsf E_1 N$.
