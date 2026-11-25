# Holding rate, with a fictitious rate one at absorbing states

Let $N$ be a [stochastic chemical reaction network](stochastic-crn.md) on a set $S$ of species with
a finite set of reactions and [total propensity](total-rate.md) $\lambda$. The holding rate of its
jump–hold chain at a state $x \in \mathbb{N}^S$ is

$$q(x) = \begin{cases} \lambda(x) & \text{if } \lambda(x) \ne 0, \\ 1 & \text{if } \lambda(x) = 0.
\end{cases}$$

A state with $\lambda(x) = 0$ is absorbing: the propensities are nonnegative, so every one of them
vanishes there and no reaction can fire. It gets the fictitious rate $1$, and the
[jump kernel](jump-pmf.md) there is the point mass at $x$, so the chain makes fictitious jumps
$x \mapsto x$, which do not move it.
