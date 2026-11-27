# Exponential moment of the square of a sub-Gaussian variable and of an empirical-mean deviation

Let $X$ be a real random variable on a probability space that is sub-Gaussian with variance proxy $c \ge 0$, i.e. $\mathbb{E}[e^{tX}] \le e^{ct^2/2}$ for all real $t$. Then for every $s \ge 0$ with $2sc < 1$,

$$
\mathbb{E}\big[e^{sX^2}\big] \le \frac{1}{\sqrt{1 - 2sc}}.
$$

Moreover, if $S_1, \dots, S_m$ ($m \ge 1$) are i.i.d. samples from a distribution $D$ and $f$ is measurable with values in $[0,1]$, then $\Delta = \mathbb{E}_D[f] - \frac1m\sum_i f(S_i)$ is sub-Gaussian with variance proxy $1/(4m)$; hence $\mathbb{E}[e^{2(m-1)\Delta^2}] \le \sqrt{m}$ for $m \ge 1$.

## Proof sketch

Write $e^{sy^2} = \mathbb{E}_g[e^{\sqrt{2s}\,y g}]$ for a standard Gaussian $g$ independent of $X$, exchange expectations, and apply the sub-Gaussian bound at $t = \sqrt{2s}\,g$; what remains is the Gaussian integral $\mathbb{E}[e^{scg^2}] = (1 - 2sc)^{-1/2}$. The empirical-mean claim is Hoeffding's lemma for each centered summand $f(S_i)/m$ (range $1/m$) and independence; taking $s = 2(m-1)$ and $c = 1/(4m)$ gives $1/\sqrt{1 - (m-1)/m} = \sqrt m$.

## Proof depends on

- [Conditional Hoeffding lemma](../has-cond-subgaussian-mgf-of-mem-icc-of-c.md)

## Sources

- W. Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58(301), 1963.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
