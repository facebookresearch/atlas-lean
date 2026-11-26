# Mixed moment growth implies mixed sub-exponential tails

Let $Y$ be a random variable and $a, b \ge 0$ such that $\|Y\|_p \le a\,p + b\sqrt{p}$ for every $p \ge 2$. Then for every $\delta \in (0, 1)$,

$$
\Pr\Big[\,|Y| \ge e\Big(a\log\frac{e}{\delta} + b\sqrt{\log\frac{e}{\delta}}\Big)\Big] \le \delta .
$$

## Proof sketch

By Markov's inequality applied to $|Y|^p$, $\Pr[|Y| \ge e\|Y\|_p] \le e^{-p}$. Choose $p = \log(e/\delta)$, so that $e^{-p} = \delta/e \le \delta$ and $e\|Y\|_p \le e(ap + b\sqrt{p})$. This requires $p \ge 2$, that is $\delta \le e^{-1}$; for $\delta > e^{-1}$ apply the bound with $p = 2$, whose threshold $e(2a + b\sqrt 2)$ is at most the stated one up to the absolute constant, and $e^{-2} \le \delta$.

## Depends on

- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Proof depends on

- [Moment form of the bounded differences inequality](bounded-differences-moment-inequality.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
