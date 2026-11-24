# The ties of the Blackwell–MacQueen urn follow the Chinese restaurant process

Let $X$ be a measurable space with measurable singletons whose σ-algebra is countably separated, let $\alpha > 0$, and let $H$ be an atomless probability measure on $X$ ($H(\{x\}) = 0$ for every $x$). For every $n$ and every partition $\pi$ of $\{0, \dots, n - 1\}$, the [tie partition](tie-partition.md) of the first $n$ draws of the [Blackwell–MacQueen urn](blackwell-mac-queen.md) equals $\pi$ with probability

$$\frac{\alpha^{|\pi|} \prod_{B \in \pi} (|B| - 1)!}{\alpha^{(n)}}, \qquad \alpha^{(n)} = \alpha(\alpha + 1) \cdots (\alpha + n - 1),$$

the law of the Chinese restaurant process with parameter $\alpha$.

## Sources

- Jim Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875, Springer (2006), DOI 10.1007/b11601500, §3.1.
