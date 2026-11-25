# Clopper–Pearson upper confidence limit

Let $n \in \mathbb{N}$ and, for $k \in \mathbb{N}$ and $p \in [0,1]$, write $P_p(X \ge k) = \sum_{i=k}^{n} \binom{n}{i} p^i (1-p)^{n-i}$ for the upper tail of the binomial law $\mathrm{Bin}(n,p)$ and $P_p(X \le k) = 1 - P_p(X \ge k+1)$ for its lower tail. After $x \in \mathbb{N}$ successes in $n$ trials, the Clopper–Pearson upper endpoint at level $\alpha \in \mathbb{R}$ is

$$U(x) = \sup\{q \in [0,1] : \alpha/2 \le P_q(X \le x)\},$$

where the supremum of the empty set is taken to be $0$. For an observation $x \le n$ at the usual level $0 < \alpha < 1$, the set is nonempty and closed: $U(x)$ is its largest element.

## Sources

- C. J. Clopper and E. S. Pearson, "The use of confidence or fiducial limits illustrated in the case of the binomial", *Biometrika* 26 (1934), 404–413.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.3.
