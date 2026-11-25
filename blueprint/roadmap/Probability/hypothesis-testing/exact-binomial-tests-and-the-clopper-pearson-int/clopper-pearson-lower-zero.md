# Lower limit after no successes

Let $n \in \mathbb{N}$ and, for $k \in \mathbb{N}$ and $p \in [0,1]$, write $P_p(X \ge k) = \sum_{i=k}^{n} \binom{n}{i} p^i (1-p)^{n-i}$ for the upper tail of the binomial law $\mathrm{Bin}(n,p)$ and $P_p(X \le k) = 1 - P_p(X \ge k+1)$ for its lower tail. For $x \in \mathbb{N}$ and $\alpha \in \mathbb{R}$ let $L(x) = \inf\{q \in [0,1] : \alpha/2 \le P_q(X \ge x)\}$ be the Clopper–Pearson lower endpoint (the infimum of the empty set is taken to be $0$). If $\alpha \le 2$, then after no successes the lower endpoint is $0$: $L(0) = 0$.

## Sources

- C. J. Clopper and E. S. Pearson, "The use of confidence or fiducial limits illustrated in the case of the binomial", *Biometrika* 26 (1934), 404–413.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.3.
