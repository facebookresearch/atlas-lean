# Perron-Frobenius for primitive stochastic matrices

**Perron–Frobenius for primitive stochastic matrices.** Let $S$ be a finite nonempty set and $P$ a row-stochastic $S \times S$ real matrix ($P_{xy} \ge 0$ and $\sum_y P_{xy} = 1$ for every $x$) that is primitive: some power $P^r$ with $r > 0$ has all entries strictly positive. Then there is $\pi : S \to \mathbb{R}$ such that:

1. $\pi$ is a stationary distribution: $\pi(y) \ge 0$ for all $y$, $\sum_y \pi(y) = 1$ and $\pi P = \pi$;
2. $\pi(y) > 0$ for every $y \in S$;
3. there are $C \in \mathbb{R}$ and $0 \le \alpha < 1$ with, for all $n \in \mathbb{N}$ and $x \in S$,

$$\frac{1}{2} \sum_{y \in S} \big\lvert (P^n)_{x y} - \pi(y) \big\rvert \le C \alpha^n;$$

4. $\pi$ is unique among all real vectors $\pi'$ with $\sum_y \pi'(y) = 1$ and $\pi' P = \pi'$, even without assuming $\pi' \ge 0$.
