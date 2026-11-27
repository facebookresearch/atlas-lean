# Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges

Let $(K_t)_{t<n}$ be a step kernel on a set $\alpha$ with adaptive process $P_n$, and let $(X_k)_{k \le n}$ be a supermartingale along it. Let $c_0, \dots, c_{n-1} \ge 0$ and suppose that for every $k < n$ and every history $h$ with $P_k(h) > 0$ there is an interval $[a, b]$ with $b - a \le c_k$ containing $X_{k+1}(h, x)$ for every $x$ in the support of $K_k(h)$ (the interval may depend on $h$). Put $C = \sum_{k<n} c_k^2$. Then for every $s \ge 0$,

$$
\mathbb{E}_{h \sim P_n}\big[e^{s (X_n(h) - X_0)}\big] \le \exp\Big(\frac{s^2 C}{8}\Big),
$$

and for every $\varepsilon \ge 0$,

$$
\Pr_{h \sim P_n}\big[X_n(h) \ge X_0 + \varepsilon\big] \le \exp\Big(-\frac{2 \varepsilon^2}{C}\Big),
$$

where the right side is read as $1$ when $C = 0$. Symmetrically, for a submartingale $\Pr[X_n \le X_0 - \varepsilon] \le e^{-2\varepsilon^2 / C}$, and for a martingale $\Pr[|X_n - X_0| \ge \varepsilon] \le 2 e^{-2\varepsilon^2 / C}$.

## Proof sketch

Fix a supported history $h$ at step $k$ and center the next value at its conditional mean $m \le X_k(h)$. The centered value lies in an interval of width at most $c_k$, so the conditional Hoeffding lemma bounds its conditional exponential moment by $e^{s^2 c_k^2/8}$; together with $m \le X_k(h)$ and $s \ge 0$ this gives the one-step factor. Iterating over $k = n-1, \dots, 0$ by the tower property yields the moment bound, and Markov's inequality with $s = 4\varepsilon / C$ gives the tail. The lower and two-sided tails follow by applying the result to $-X$ and a union bound.

## Depends on

- [Finite-horizon adaptive discrete process and its supermartingales](finite-horizon-adaptive-discrete-process.md)

## Proof depends on

- [Conditional Hoeffding lemma](../has-cond-subgaussian-mgf-of-mem-icc-of-c.md)
- [Azuma's inequality](../azuma-inequality.md)

## Sources

- K. Azuma, "Weighted Sums of Certain Dependent Random Variables", Tohoku Mathematical Journal 19(3), 1967.
- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58(301), 1963.
