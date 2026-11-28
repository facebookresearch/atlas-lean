# Trade-off functions of pairs of distributions

Let $P$ and $Q$ be probability distributions on a common measurable space. For a rejection rule $\phi$ (a measurable function with values in $[0,1]$ giving the probability of rejecting the null hypothesis $P$), the type I error is $\alpha_\phi = \mathbb{E}_P[\phi]$ and the type II error is $\beta_\phi = 1 - \mathbb{E}_Q[\phi]$. The **trade-off function** of $P$ and $Q$ is

$$
T(P, Q)(\alpha) = \inf\{\beta_\phi : \alpha_\phi \le \alpha\}, \qquad \alpha \in [0,1],
$$

the smallest type II error achievable at type I error at most $\alpha$. The infimum is attained by likelihood ratio tests: dominate $P$ and $Q$ by $\mu = P + Q$ and take densities $p, q$. For $\alpha \in (0,1]$ choose a finite threshold $k \ge 0$ and a randomization on $\{q = kp\}$ giving a test $\varphi^\star$ that rejects on $\{q > kp\}$ and has $\mathbb{E}_P[\varphi^\star] = \alpha$ (at $\alpha = 1$, $k = 0$ with full randomization, so the test always rejects); it is most powerful by the Neyman–Pearson lemma. At $\alpha = 0$ no finite threshold need work (for two normal distributions with different means every finite $k$ gives positive size); the optimal test has threshold $k = +\infty$ and rejects exactly on $\{p = 0 < q\}$, a $P$-null set, since a test of size $0$ vanishes $\mu$-almost everywhere on $\{p > 0\}$. For functions $f, g$ on $[0,1]$ write $f \ge g$ if $f(\alpha) \ge g(\alpha)$ for all $\alpha$; larger trade-off functions mean the two distributions are harder to distinguish, and $T(P, P)(\alpha) = 1 - \alpha$.

## Proof depends on

- [Neyman–Pearson lemma](../../../../Probability/hypothesis-testing/neyman-pearson-dominated-two-simple.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
