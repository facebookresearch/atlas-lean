# Fundamental sequences of Zeckendorf collections

Let $E$ be a Zeckendorf collection and
index coefficient functions and sequences from $0$. Suppose that, for each $m \ge 1$,
$\theta^{(m)}$ is the immediate predecessor in $E$ of the coefficient function with entry $1$ at
index $m$ and $0$ elsewhere. For a sequence $H$ write $\mathrm{eval}_H(\mu) = \sum_k \mu_k H_k$.
Then there is a unique strictly increasing sequence $H$ of positive integers such that
$\mathrm{eval}_H$ is a bijection from $E$ onto $\mathbb N$. Moreover, every such $H$ satisfies
$H_m = H_0 + \mathrm{eval}_H(\theta^{(m)})$ for all $m \ge 1$, and for all $\mu, \nu \in E$,
$\mu \lt _a \nu$ (that is, $\mu_k < \nu_k$ at the largest index $k$ where $\mu$ and $\nu$ differ)
if and only if $\mathrm{eval}_H(\mu) < \mathrm{eval}_H(\nu)$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Theorem 5 (`integers-2025-A25-thm-5`; arXiv:2308.12872v1, Section 2.2, quoting Chang 2021).
