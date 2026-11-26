# Trade-off functions of pairs of distributions

Let $P$ and $Q$ be probability distributions on a common measurable space. For a rejection rule $\phi$ (a measurable function with values in $[0,1]$ giving the probability of rejecting the null hypothesis $P$), the type I error is $\alpha_\phi = \mathbb{E}_P[\phi]$ and the type II error is $\beta_\phi = 1 - \mathbb{E}_Q[\phi]$. The **trade-off function** of $P$ and $Q$ is

$$
T(P, Q)(\alpha) = \inf\{\beta_\phi : \alpha_\phi \le \alpha\}, \qquad \alpha \in [0,1],
$$

the smallest type II error achievable at type I error at most $\alpha$. By the Neyman–Pearson lemma the infimum is attained by likelihood ratio tests. For functions $f, g$ on $[0,1]$ write $f \ge g$ if $f(\alpha) \ge g(\alpha)$ for all $\alpha$; larger trade-off functions mean the two distributions are harder to distinguish, and $T(P, P)(\alpha) = 1 - \alpha$.

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
