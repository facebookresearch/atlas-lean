# One-sided coverage of the Clopper–Pearson lower limit

Let $X : \Omega \to \mathbb{N}$ be a random variable with law $\mathrm{Bin}(n,p)$ under a measure $P$ on $\Omega$ (so $P$ is a probability measure), where $n \in \mathbb{N}$ and $p \in [0,1]$, and let $0 < \alpha < 1$. Write $L(x)$ and $U(x)$ for the Clopper–Pearson endpoints at level $\alpha$ after $x$ successes in $n$ trials: $L(x) = \inf\{q \in [0,1] : \alpha/2 \le T^{+}_q(x)\}$ and $U(x) = \sup\{q \in [0,1] : \alpha/2 \le T^{-}_q(x)\}$, where $T^{+}_q(k) = \sum_{i=k}^{n} \binom{n}{i} q^i (1-q)^{n-i}$ is the binomial upper tail and $T^{-}_q(k) = 1 - T^{+}_q(k+1)$ the lower tail (the infimum and supremum of the empty set are taken to be $0$). Then the lower endpoint is a lower confidence bound of level $1 - \alpha/2$:

$$P\big(L(X) \le p\big) \ge 1 - \frac{\alpha}{2}.$$

## Sources

- C. J. Clopper and E. S. Pearson, "The use of confidence or fiducial limits illustrated in the case of the binomial", *Biometrika* 26 (1934), 404–413.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.3.
