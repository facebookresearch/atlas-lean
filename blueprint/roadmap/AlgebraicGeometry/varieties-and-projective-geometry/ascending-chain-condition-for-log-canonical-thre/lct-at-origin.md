# Real-valued analytic log canonical threshold at the origin

For natural numbers $n, r$ and polynomials $f_1, \dots, f_r \in \mathbb{C}[x_1, \dots, x_n]$, the real-valued analytic log canonical threshold at the origin is the real number

$$\operatorname{lct}_0(f) = \sup \Big\{ c \in \mathbb{R} : c \ge 0,\ \exists\, \varepsilon > 0,\ z \mapsto \Big(\sum_{i=1}^{r} |f_i(z)|^2\Big)^{-c} \text{ is integrable on } B(0, \varepsilon) \Big\},$$

where $B(0,\varepsilon) \subseteq \mathbb{C}^n$ is the open ball (sup norm) with respect to Lebesgue measure on $\mathbb{C}^n$.

Conventions: the power is the real power of a nonnegative real, with $0^{-c} = 0$ for $c \neq 0$ and $0^0 = 1$; the supremum is taken in $\mathbb{R}$, so it equals $0$ when the set is unbounded above.

For a nonzero ideal $(f_1, \dots, f_r)$ vanishing at the origin, this real number is the classical log canonical threshold $\operatorname{lct}_0$ of the ideal at the origin (M. Mustaţă, IMPANGA lecture notes on log canonical thresholds, Theorem 1.2), and those are the only ideals the [ascending chain condition](lct-ascending-chain-condition.md) concerns. It differs from the classical invariant elsewhere: for $n = r = 1$ and $f_1 = 1$, a unit, every $c \ge 0$ qualifies, so the set is unbounded and the real supremum is $0$, whereas the classical threshold of the unit ideal is $+\infty$.
