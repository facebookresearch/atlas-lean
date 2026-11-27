# Azuma-Hoeffding tails for adaptively generated event counts

Let $(K_t)_{t<n}$ be a step kernel on a set $\alpha$ with adaptive process $P_n$, and for each $t < n$ and history $h \in \alpha^t$ let $E_t(h) \subseteq \alpha$ be an event. Let $N(h) = |\{t < n : x_t \in E_t(x_0, \dots, x_{t-1})\}|$ be the number of successes along $h = (x_0, \dots, x_{n-1})$, and let $p_0, \dots, p_{n-1} \in [0,1]$. If $K_t(h)(E_t(h)) \le p_t$ for every $t < n$ and every supported history $h \in \alpha^t$, then for every $\varepsilon \ge 0$

$$
\Pr_{h \sim P_n}\Big[N(h) \ge \sum_{t<n} p_t + \varepsilon\Big] \le \exp\Big(-\frac{2\varepsilon^2}{n}\Big).
$$

If instead $K_t(h)(E_t(h)) \ge p_t$ throughout, then $\Pr[N(h) \le \sum_t p_t - \varepsilon] \le \exp(-2\varepsilon^2/n)$.

## Proof sketch

The process $X_k = N_k - \sum_{t<k} p_t$, where $N_k$ counts successes among the first $k$ steps, is a supermartingale (respectively submartingale) whose next value given a history ranges over an interval of width $1$. Apply the Azuma-Hoeffding inequality with $c_k = 1$.

## Depends on

- [Finite-horizon adaptive discrete process and its supermartingales](finite-horizon-adaptive-discrete-process.md)

## Proof depends on

- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](azuma-hoeffding-bounded-conditional-ranges.md)

## Sources

- K. Azuma, "Weighted Sums of Certain Dependent Random Variables", Tohoku Mathematical Journal 19(3), 1967.
- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58(301), 1963.
