# Relaxation time controls mixing: upper and lower bounds

Let $P$ be reversible with respect to $\pi$ on a finite set with at least two states, $\pi_{\min} = \min_x \pi(x) > 0$, contraction factor $\lambda_\ast$ and absolute spectral gap $\gamma_\ast$.

1. (Upper bound) If $\gamma_\ast > 0$, then for $0 < \varepsilon < 1$,

$$
t_{\mathrm{mix}}(\varepsilon) \le \max\Bigl(0, \Bigl\lceil \frac{1}{\gamma_\ast}\Bigl(\tfrac12\log\frac{1}{\pi_{\min}} + \log\frac{1}{2\varepsilon}\Bigr)\Bigr\rceil\Bigr) \le \max\Bigl(0, \Bigl\lceil \frac{1}{\gamma_\ast}\log\frac{1}{\varepsilon\,\pi_{\min}}\Bigr\rceil\Bigr) ,
$$

the least nonnegative integer at least the bracketed quantity (the ceiling alone can be negative when $\varepsilon$ is close to $1$).

2. (Lower bound) For every $t \in \mathbb{N}$, $\lambda_\ast^t \le 2\,d(t)$ (with $0^0 = 1$), including the endpoint cases $\lambda_\ast \in \{0, 1\}$. Consequently, for $0 < \varepsilon < 1/2$: if $0 < \lambda_\ast < 1$, then $(\gamma_\ast^{-1} - 1)\log\frac{1}{2\varepsilon} \le t_{\mathrm{mix}}(\varepsilon)$; if $\lambda_\ast = 1$ (that is, $\gamma_\ast = 0$), then $d(t) \ge 1/2$ for every $t$ and $t_{\mathrm{mix}}(\varepsilon) = \infty$; if $\lambda_\ast = 0$ (that is, $\gamma_\ast = 1$), the bound reads $0 \le t_{\mathrm{mix}}(\varepsilon)$.

## Proof sketch

The upper bound follows from the total-variation consequence of chi-square contraction together with $\lambda_\ast^t \le e^{-\gamma_\ast t}$. For the lower bound, take an eigenfunction $f$ with eigenvalue of modulus $\lambda_\ast$; it has $\pi$-mean zero, so $|\lambda_\ast^t f(x)| = |\sum_y (P^t(x,y) - \pi(y)) f(y)| \le 2 d(t) \|f\|_\infty$, and evaluating at a maximizer of $|f|$ gives $\lambda_\ast^t \le 2d(t)$ for every $\lambda_\ast \in [0,1]$. If $\lambda_\ast = 1$ this forces $d(t) \ge 1/2 > \varepsilon$ at every $t$. If $0 < \lambda_\ast < 1$, taking logarithms at $t = t_{\mathrm{mix}}(\varepsilon)$ gives $t_{\mathrm{mix}}(\varepsilon) \ge \log\frac{1}{2\varepsilon} / \log\frac{1}{\lambda_\ast}$, and $\log(1/\lambda_\ast) \le 1/\lambda_\ast - 1 = \gamma_\ast/(1-\gamma_\ast)$. In the upper bound, the contraction estimate holds at every $t$ at least the bracketed quantity, so the first nonnegative such integer suffices.

## Depends on

- [Absolute spectral gap and l2 contraction factor of a reversible chain](absolute-spectral-gap.md)
- [Distance to stationarity and total-variation mixing time](../coupling-and-total-variation-mixing/distance-to-stationarity-and-mixing-time.md)

## Proof depends on

- [Chi-square contraction and pointwise transition bounds for reversible chains](chi-square-contraction-reversible-chain.md)
- [Basic inequalities for total-variation mixing](../coupling-and-total-variation-mixing/total-variation-mixing-inequalities.md)
- [Mixing of a lazy reversible chain from its spectral gap](../../dirichlet-forms/is-mixed-at-of-le-spectral-gap.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
