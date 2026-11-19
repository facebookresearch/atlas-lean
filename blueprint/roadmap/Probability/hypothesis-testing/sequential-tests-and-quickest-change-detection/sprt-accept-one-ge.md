# Wald's inequality on the acceptance of the alternative

Let $P_0$ and $P_1$ be mutually absolutely continuous probability measures on a measurable space $\mathcal{X}$ ($P_1 \ll P_0$ and $P_0 \ll P_1$), and let the observations $X_1, X_2, \dots$ be the coordinates of $\omega \in \mathcal{X}^{\mathbb{N}}$, $X_{i+1}(\omega) = \omega_i$. Write $L = dP_1/dP_0$ (a real number almost everywhere) and $\Lambda_n = \sum_{i=1}^n \log L(X_i)$. For all $a, b \in \mathbb{R}$, the [SPRT](sprt-time.md) with log-boundaries $a$ and $b$ and stopping time $N$ satisfies

$$e^b\, P_0^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \ge b) \le P_1^{\otimes \mathbb{N}}(N < \infty,\ \Lambda_N \ge b).$$

This is the second line of Wald's inequalities, $1 - \beta = \int_{\lambda_N \ge B} \lambda_N \, dP_0 \ge B \alpha$ (Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2), whose upper boundary $B$ is $e^b$ in the notation above). With the [first inequality](sprt-accept-zero-le.md) it gives Wald's approximations $e^b \approx (1 - \beta)/\alpha$ and $e^a \approx \beta/(1 - \alpha)$, which are equalities when the log-likelihood ratio has no overshoot. The source takes $a < 0 < b$; the inequality holds for all $a$ and $b$.

The proof is the same as for the first inequality, with $R_n = e^{\Lambda_n} \ge e^b$ on $\{N = n,\ \Lambda_n \ge b\}$.

## Sources

- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3), second line of (a2), and the approximations stated after it.

## Informally uses

- [Likelihood-ratio change of measure on the first $n$ observations](infinite-pi-apply-eq-set-lintegral-prod.md)
- [The SPRT stopping time is a stopping time](is-stopping-time-sprt-time.md)

## Background

- [Wald's equation](../../martingales/wald-s-equations/wald-equation.md): the identity $\mathsf E\,\Lambda_N = \mathsf E\,\Lambda_1 \cdot \mathsf E\, N$ behind Wald's approximations to the average sample number.
