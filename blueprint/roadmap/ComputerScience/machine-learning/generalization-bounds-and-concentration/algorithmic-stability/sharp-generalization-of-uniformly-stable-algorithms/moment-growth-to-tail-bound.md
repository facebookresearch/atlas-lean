# Mixed moment growth implies mixed sub-exponential tails

Let $Y$ be a random variable and $a, b \ge 0$ such that $\|Y\|_p \le a\,p + b\sqrt{p}$ for every $p \ge 2$. Then for every $\delta \in (0, 1)$, with $p_\delta = \max\{2, \log(e/\delta)\}$,

$$
\Pr\Big[\,|Y| > e\big(a\,p_\delta + b\sqrt{p_\delta}\big)\Big] \le \delta ,
$$

that is, $|Y| \le e(a\,p_\delta + b\sqrt{p_\delta})$ with probability at least $1 - \delta$. If the moment bound holds for every $p \ge 1$, the same argument with $p = \log(e/\delta) \ge 1$ gives Lemma 1 of Bousquet, Klochkov and Zhivotovskiy: $|Y| \le e\big(a\log(e/\delta) + b\sqrt{\log(e/\delta)}\big)$ with probability at least $1 - \delta$.

## Proof sketch

Take $p = p_\delta \ge 2$. If $\|Y\|_p = 0$ then $Y = 0$ almost surely and the event has probability $0$. Otherwise Markov's inequality applied to $|Y|^p$ gives $\Pr[|Y| > e\|Y\|_p] \le e^{-p}$, and the threshold satisfies $e(a p + b\sqrt{p}) \ge e\|Y\|_p$, so the probability is at most $e^{-p_\delta} \le e^{-\log(e/\delta)} = \delta/e \le \delta$. The strict inequality matters: for $Y = 0$ and $a = b = 0$ the event $|Y| \ge 0$ has probability $1$.

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
