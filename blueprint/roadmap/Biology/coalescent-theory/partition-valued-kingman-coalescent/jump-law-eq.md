# Kingman's formula

For natural numbers $m < n$ and every partition $\pi \in \mathcal{P}_n$, the [law of the jump chain](jump-law.md) after $m$ jumps, started from singletons, is

$$J_n^m(\bot, \pi) = \begin{cases} p_n(\pi) & \text{if } |\pi| + m = n, \\ 0 & \text{otherwise,} \end{cases}$$

where $p_n(\pi) = (n-k)!\, k!\, (k-1)! \prod_{B \in \pi} |B|! / (n!\,(n-1)!)$ with $k = |\pi|$ is [Kingman's formula](kingman-prob.md). For $m \ge n - 1$ the chain has been absorbed at the partition with one block.

## Sources

- J. F. C. Kingman, *The coalescent*, Stochastic Process. Appl. 13 (1982), 235–248.
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), ch. 1.
