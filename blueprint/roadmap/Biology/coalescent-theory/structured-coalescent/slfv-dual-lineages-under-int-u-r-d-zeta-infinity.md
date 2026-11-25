# Spatial Λ-Fleming–Viot lineages exist when ∫ u r^d ζ is finite

In the setting of the [lineages of the spatial Λ-Fleming–Viot model](slfv-dual-lineages-bounded-radius-and-finite-eve.md), drop the bounds on the radius and on the mass of $\zeta$, and assume only

$$\Lambda_1 = \int u\, V_d r^d\, \zeta(dr, du) < \infty ,$$

the $d$-dimensional form of Barton, Etheridge and Véber's Assumption 2.4. The measure $\zeta$ may then have infinite mass near $u = 0$. Each block is affected by events at rate
$\Lambda_1$, so with $k \le n$ blocks the rate of events affecting at least one block is at most $k\Lambda_1$. The $n$-lineage process is therefore well defined as [a kernel on a
Poisson clock](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md) of rate $n\Lambda_1$. In each step the kernel picks a label $i \in \{1, \dots, n\}$ uniformly and stays put unless $i$ is the least label of its block; otherwise it draws $(r, u)$ proportional to
$u\, V_d r^d\, \zeta$ and a center $x$ uniform in the ball of radius $r$ around $i$'s block, declares $i$'s block affected, lets each other block in $B(x, r)$ be affected with
probability $u$, and keeps the event only if $i$'s block is the lowest-labelled affected block. Under this kernel, the rate of an event affecting exactly a given set $A$ of blocks
equals its rate under the Poisson event description: it is generated only through the least label $i$ of $A$, which is selected at rate $\Lambda_1$, so events with radius in $dr$,
impact in $du$ and center in $dx$ covering $i$'s block arrive at rate $u\, \zeta(dr, du)\, dx$, the Poisson rate times the probability $u$ that $i$'s block is affected, and the other blocks are
then affected independently with probability $u$ as in the Poisson description. With bounded radius and finite $\zeta$ it is the process
of the bounded case. If $\Lambda_1 = 0$ the process is constant. The process is a Poisson-clocked state-dependent Markov process, not an additive compound Poisson
process, when $n \ge 2$.

## Depends on

- [Lineages of the spatial Λ-Fleming–Viot model with bounded event radius](slfv-dual-lineages-bounded-radius-and-finite-eve.md)
- [A Markov kernel run on a Poisson clock is a pure-jump Markov process](../../../Probability/markov-chains/construction-of-markov-chains/uniformized-pure-jump-markov-process-on-a-polish.md)

## Sources

- N. H. Barton, A. M. Etheridge and A. Véber, "A new model for evolution in a spatial continuum", arXiv:0904.0210 (2010), Assumption 2.4 (condition (5)) and the discussion after it (stated there for $d = 2$).
