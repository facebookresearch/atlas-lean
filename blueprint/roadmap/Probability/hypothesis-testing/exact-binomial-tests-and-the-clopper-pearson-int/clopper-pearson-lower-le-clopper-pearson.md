# The Clopper–Pearson interval is nonempty

Let $n \in \mathbb{N}$ and, for $k \in \mathbb{N}$ and $p \in [0,1]$, write $P_p(X \ge k) = \sum_{i=k}^{n} \binom{n}{i} p^i (1-p)^{n-i}$ for the upper tail of the binomial law $\mathrm{Bin}(n,p)$ and $P_p(X \le k) = 1 - P_p(X \ge k+1)$ for its lower tail. For $x \in \mathbb{N}$ and $\alpha \in \mathbb{R}$ let $L(x) = \inf\{q \in [0,1] : \alpha/2 \le P_q(X \ge x)\}$ and $U(x) = \sup\{q \in [0,1] : \alpha/2 \le P_q(X \le x)\}$ be the Clopper–Pearson endpoints (the infimum and supremum of the empty set are taken to be $0$). If $x \le n$ and $0 < \alpha \le 1$, then $L(x) \le U(x)$.

## Sources

- C. J. Clopper and E. S. Pearson, "The use of confidence or fiducial limits illustrated in the case of the binomial", *Biometrika* 26 (1934), 404–413.
- G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §9.2.3.
