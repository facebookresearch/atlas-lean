# FKG inequality

Let $E$ be a finite set and order $\{0,1\}^E$ coordinatewise. Let $\pi : \{0,1\}^E \to \mathbb{R}$ be a probability weight, that is, $\pi \ge 0$ and $\sum_\omega \pi(\omega) = 1$, satisfying the FKG lattice condition

$$\pi(\omega)\,\pi(\omega') \le \pi(\omega \vee \omega')\,\pi(\omega \wedge \omega') \quad \text{for all } \omega, \omega'.$$

Then any two monotone functions $f, g : \{0,1\}^E \to \mathbb{R}$ are positively correlated under $\pi$:

$$\Big(\sum_\omega \pi(\omega) f(\omega)\Big)\Big(\sum_\omega \pi(\omega) g(\omega)\Big) \le \sum_\omega \pi(\omega) f(\omega) g(\omega).$$

No sign condition is imposed on $f$ and $g$: the case of nonnegative functions and an unnormalised weight implies the general one after shifting $f$ and $g$ by their values at the all-zero configuration.

## Sources

- C. M. Fortuin, P. W. Kasteleyn and J. Ginibre, *Correlation inequalities on some partially ordered sets*, Comm. Math. Phys. 22 (1971), 89–103.
