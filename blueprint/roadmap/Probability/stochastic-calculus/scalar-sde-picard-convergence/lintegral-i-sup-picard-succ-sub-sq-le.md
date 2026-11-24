# Factorial maximal bound for scalar Picard increments

Let $B$ have real Brownian finite-dimensional laws, be adapted to a filtration $(\mathcal F_t)$, and have each increment $B_t-B_s$ independent of $\mathcal F_s$ for $s\le t$. Let $\sigma,b:\mathbb R\to\mathbb R$ be globally Lipschitz with a common constant $K\ge0$, and fix $x\in\mathbb R$.

Suppose $X^0_t=x$ and the actual all-time Picard sequence satisfies

$$X^{n+1}_t=x+J^n_t+\int_0^t b(X^n_s)\,ds$$

for every sample and time. Each $X^n$ is progressive, continuous on every path, and has finite integrated second moment on every finite horizon. Each $J^n$ is a progressive martingale continuous on every path, and at each fixed time equals the actual Itô integral of $\sigma(X^n)$ almost surely.

For $T\ge0$, put

$$C_T=8\sigma(x)^2+2T b(x)^2,\qquad A_T=2(4+T)K^2.$$

For every integer $n\ge0$ and every $0\le t\le T$,

$$\mathbb E\sup_{0\le s\le t}|X^{n+1}_s-X^n_s|^2
\le C_T A_T^n\frac{t^{n+1}}{(n+1)!}.$$

The expectation is a nonnegative extended integral. Brownian finite-dimensional laws imply probability normalization. The bound includes $t=0$, $K=0$, and vanishing coefficients. No filtration completeness, right continuity, or continuous driving paths are needed for this estimate. No convergence of the sequence is assumed.

The initial increment has bound $C_Tt$. The maximal difference estimate bounds the next increment by $A_T$ times the integral of the previous running-maximum moment. Repeated integration yields the factorial. This is the Picard convergence argument in Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (2016), Theorem 8.3; the displayed constants are sufficient and nonoptimal.
