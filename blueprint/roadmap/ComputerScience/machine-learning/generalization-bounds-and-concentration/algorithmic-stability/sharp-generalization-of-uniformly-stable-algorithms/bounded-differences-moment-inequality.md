# Moment form of the bounded differences inequality

Let $f$ be a measurable function of independent random variables $X_1, \dots, X_n$, with values in a common space $\mathcal{X}$, such that changing any single coordinate of the argument changes $f$ by at most $\beta$. Then for every $p \ge 2$,

$$
\big\| f(X_1, \dots, X_n) - \mathbb{E} f(X_1, \dots, X_n) \big\|_p \le 2\sqrt{np}\,\beta .
$$

## Proof sketch

By McDiarmid's inequality, $f - \mathbb{E}f$ is sub-Gaussian with variance proxy $n\beta^2/4$, so $\Pr[|f - \mathbb{E}f| \ge t] \le 2e^{-2t^2/(n\beta^2)}$. Integrating the tail, $\mathbb{E}|f - \mathbb{E}f|^p = \int_0^\infty p t^{p-1}\Pr[|f - \mathbb{E}f| \ge t]\,dt \le 2\Gamma(p/2+1)(n\beta^2/2)^{p/2}$, and Stirling's bound $\Gamma(p/2+1)^{1/p} \le \sqrt{p}$ gives the claim.

## Proof depends on

- [McDiarmid's inequality, upper tail](../../../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/measure-real-sub-integral-ge-le-of-bound.md)
- [McDiarmid's inequality, lower tail](../../../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/measure-real-integral-sub-ge-le-of-bound.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833, Lemma 2.
