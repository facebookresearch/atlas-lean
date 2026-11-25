# Itô's formula for continuous semimartingales with bounded derivatives

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ be a filtered probability space and $X=X_0+M+A$ a continuous semimartingale: $X_0$ is $\mathcal F_0$-measurable, $M$ is a continuous local martingale with $M_0=0$, and $A$ is a continuous adapted process of finite variation on bounded intervals with $A_0=0$. Let $\langle M\rangle$ be the [quadratic variation process](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md) of $M$. Let $f:\mathbb R\to\mathbb C$ be twice continuously differentiable with $f'$ and $f''$ bounded. Then, almost surely, for all $t\ge0$,

$$f(X_t)=f(X_0)+\int_0^tf'(X_s)\,dM_s+\int_0^tf'(X_s)\,dA_s+\frac12\int_0^tf''(X_s)\,d\langle M\rangle_s,$$

where the first integral is the [stochastic integral against a continuous local martingale](../it-integral/stochastic-integral-against-continuous-local-mar.md), applied to real and imaginary parts, and the last two are pathwise Lebesgue–Stieltjes integrals. For $M=B$ a Brownian motion, $A=0$ and real $f$, this is [Itô's formula](ito-formula.md).

## Depends on

- [Quadratic variation process $\langle M\rangle$ for continuous local martingales](../../martingales/quadratic-variation-of-continuous-local-martingales/quadratic-variation-process-m-for-continuous-loc.md)
- [Stochastic integral against continuous local martingales (localized)](../it-integral/stochastic-integral-against-continuous-local-mar.md)

## Expansion

A full proof page must establish the following.

- Reduction to real $f$ by linearity, and localization: stop at times $\tau_n$ at which $|M|$, $\langle M\rangle$ and the total variation of $A$ reach $n$, so that all three are bounded.
- Second-order Taylor expansion along partitions with mesh tending to $0$: the first-order terms converge to the stochastic and Stieltjes integrals, the second-order terms $\frac12\sum f''(X_{t_k})(X_{t_{k+1}}-X_{t_k})^2$ converge to $\frac12\int f''(X)\,d\langle M\rangle$ in probability (cross terms with $A$ and the $A$-squared terms vanish by continuity and finite variation), and the remainder vanishes by uniform continuity of $f''$ on compacts.
- Passage to a version holding simultaneously for all $t$, by continuity of both sides.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren der mathematischen Wissenschaften 293, Springer (1999), <https://link.springer.com/book/10.1007/978-3-662-06400-9>, Itô's formula for continuous semimartingales (statement and proof).
