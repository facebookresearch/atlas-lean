# Failure probability of a streaming algorithm

Let $A$ be a [randomized streaming algorithm](streaming-algorithm.md) over an alphabet $\alpha$ with seeds in a finite nonempty set $R$, let $\mathrm{ok}(l, y)$ be a predicate saying that the output $y \in \mathbb{R}$ is acceptable on the stream $l$, and let $l$ be a stream. The failure probability of $A$ on $l$ is

$$\frac{\#\{r \in R : \text{not } \mathrm{ok}(l, A_r(l))\}}{|R|},$$

where $A_r(l)$ is the [output](output.md) of $A$ with seed $r$ on $l$: the probability that the output is not acceptable when the seed is uniform on $R$.
