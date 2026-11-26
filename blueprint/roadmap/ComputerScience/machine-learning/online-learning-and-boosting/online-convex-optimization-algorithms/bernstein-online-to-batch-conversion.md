# Variance-sensitive online-to-batch conversion via Bernstein's inequality for martingales

Let $z_0, \ldots, z_{T-1}$ be i.i.d. from $D$, $T > 0$, $\delta \in (0,1]$. Suppose an online learner commits in round $t$ to a function $f_t : Z \to [a, b]$ depending only on $z_0, \ldots, z_{t-1}$, whose conditional variance under $D$ is at most $s_t$. Then with probability at least $1 - \delta$,

$$
\frac1T\sum_{t<T}\mathbb{E}_{z\sim D} f_t(z) \le \frac1T\sum_{t<T} f_t(z_t) + \frac1T\sqrt{2\Big(\sum_{t<T}s_t\Big)\ln\frac1\delta} + \frac{2(b-a)\ln(1/\delta)}{3T}.
$$

Corollary for convex losses: if $\ell(\cdot, z)$ is convex on a convex set $K$, $u \in K$, $|\ell(w,z) - \ell(u,z)| \le c$ on $K$, the excess loss $\ell(w_t, \cdot) - \ell(u, \cdot)$ of the learner's iterate $w_t$ has conditional variance at most $s$, and the online regret against $u$ is at most $R$ on every sample, then with probability at least $1-\delta$ the average iterate $\bar w$ has risk $L_D(\bar w) \le L_D(u) + R/T + \sqrt{2 s\ln(1/\delta)/T} + 4c\ln(1/\delta)/(3T)$. When $s = 0$ the deviation is of order $1/T$.

## Proof sketch

The differences $\mathbb{E}f_t - f_t(z_t)$ form a martingale difference sequence for the natural filtration, with ranges at most $b - a$ and conditional variances at most $s_t$. Bernstein's inequality for such sums (in product-measure form) gives the first bound. For the corollary apply it to the excess losses and use Jensen's inequality to pass from the average risk of the iterates to the risk of the average iterate.

## Depends on

- [Online-to-batch conversion](../online-to-batch-conversion.md)

## Proof depends on

- [Bernstein's inequality for bounded variables, upper tail](../../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/measure-real-ge-le-bernstein.md)
- [Online-to-batch conversion](../online-to-batch-conversion.md)

## Sources

- Nicolò Cesa-Bianchi, Alex Conconi and Claudio Gentile, "On the Generalization Ability of On-Line Learning Algorithms", IEEE Transactions on Information Theory, 2004.
- David A. Freedman, "On Tail Probabilities for Martingales", The Annals of Probability, 1975.
