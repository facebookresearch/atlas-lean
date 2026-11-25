# Coalescent model linking heterozygosity and coalescence times

Let $\mu$ be a measure on a measurable space $\Omega$ and $P$ a set of populations. A coalescent model consists of allele frequencies $p_X : \Omega \to \mathbb{R}$ ($X \in P$), square integrable with respect to $\mu$, a real number $\theta$ and real numbers $T(X, Y)$ for $X, Y \in P$ such that

$$\pi(X, Y) = \theta\, T(X, Y) \qquad \text{for all } X, Y \in P,$$

where $\pi$ is the [mean heterozygosity](mean-het.md). The parameters are arbitrary reals satisfying this relation. When $\mu$ is a probability measure, $\theta \ge 0$ is the scaled mutation rate ($\theta = 4Nu$) and the $T(X, Y) \ge 0$ are finite expected pairwise coalescence times (in units of $2N$ generations), it is the infinite-sites relation under neutral mutation, taken as an assumption; for $\theta = 0$ the times are not determined by the frequencies.
