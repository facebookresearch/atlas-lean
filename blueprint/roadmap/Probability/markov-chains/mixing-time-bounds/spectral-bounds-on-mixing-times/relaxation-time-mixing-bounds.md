# Relaxation time controls mixing: upper and lower bounds

Let $P$ be irreducible and reversible with respect to $\pi$ on a finite set with at least two states, $\pi_{\min} = \min_x \pi(x) > 0$, contraction factor $\lambda_\ast$ and absolute spectral gap $\gamma_\ast$.

1. (Upper bound) If $\gamma_\ast > 0$, then for $0 < \varepsilon < 1$,

$$
t_{\mathrm{mix}}(\varepsilon) \le \max\Bigl(0, \Bigl\lceil \frac{1}{\gamma_\ast}\Bigl(\tfrac12\log\frac{1}{\pi_{\min}} + \log\frac{1}{2\varepsilon}\Bigr)\Bigr\rceil\Bigr) \le \max\Bigl(0, \Bigl\lceil \frac{1}{\gamma_\ast}\log\frac{1}{\varepsilon\,\pi_{\min}}\Bigr\rceil\Bigr) ,
$$

the least nonnegative integer at least the bracketed quantity (the ceiling alone can be negative when $\varepsilon$ is close to $1$).

2. (Lower bound) If $P$ is moreover aperiodic, then $\gamma_\ast > 0$, and for every $t \in \mathbb{N}$, $\lambda_\ast^t \le 2\,d(t)$ (with $0^0 = 1$). Consequently, for $0 < \varepsilon < 1/2$, $(\gamma_\ast^{-1} - 1)\log\frac{1}{2\varepsilon} \le t_{\mathrm{mix}}(\varepsilon)$.

## Proof sketch

The upper bound follows from the total-variation consequence of chi-square contraction together with $\lambda_\ast^t \le e^{-\gamma_\ast t}$. For the lower bound, take an eigenfunction $f$ with eigenvalue $\lambda \ne 1$ of modulus $\lambda_\ast$; it has $\pi$-mean zero, so $|\lambda^t f(x)| = |\sum_y (P^t(x,y) - \pi(y)) f(y)| \le 2 d(t) \|f\|_\infty$, and evaluating at a maximizer of $|f|$ gives $\lambda_\ast^t \le 2d(t)$. Taking logarithms at $t = t_{\mathrm{mix}}(\varepsilon)$ gives $t_{\mathrm{mix}}(\varepsilon)\log\frac{1}{\lambda_\ast} \ge \log\frac{1}{2\varepsilon}$, and $\log(1/\lambda_\ast) \le 1/\lambda_\ast - 1 = \gamma_\ast/(1-\gamma_\ast)$; if $\lambda_\ast = 0$ the bound reads $0 \le t_{\mathrm{mix}}(\varepsilon)$. In the upper bound, the contraction estimate holds at every $t$ at least the bracketed quantity, so the first nonnegative such integer suffices.

The following extension is derived here and is not stated in the cited source. Without aperiodicity, the inequality $\lambda_\ast^t \le 2\,d(t)$ still holds for every $t$, by the same argument, since an irreducible chain has $1$ as a simple eigenvalue. If $\lambda_\ast = 1$ (that is, $\gamma_\ast = 0$, which for an irreducible chain happens exactly when it is periodic, with eigenvalue $-1$), this forces $d(t) \ge 1/2$ for every $t$, so $t_{\mathrm{mix}}(\varepsilon) = \infty$ for $0 < \varepsilon < 1/2$.

## Depends on

- [Irreducible stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/is-irreducible.md)
- [Absolute spectral gap and l2 contraction factor of a reversible chain](absolute-spectral-gap.md)
- [Distance to stationarity and total-variation mixing time](../coupling-and-total-variation-mixing/distance-to-stationarity-and-mixing-time.md)

## Proof depends on

- [Chi-square contraction and pointwise transition bounds for reversible chains](chi-square-contraction-reversible-chain.md)
- [Basic inequalities for total-variation mixing](../coupling-and-total-variation-mixing/total-variation-mixing-inequalities.md)
- [Mixing of a lazy reversible chain from its spectral gap](../../dirichlet-forms/is-mixed-at-of-le-spectral-gap.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017, Section 12.2, Theorem 12.4, Theorem 12.5 and (12.15).
