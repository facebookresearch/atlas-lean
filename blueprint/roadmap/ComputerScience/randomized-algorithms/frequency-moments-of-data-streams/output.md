# Output of a streaming algorithm

Let $A$ be a [randomized streaming algorithm](streaming-algorithm.md) with $s$ bits of memory over an alphabet $\alpha$, with initial states $\mathrm{init}_r$, transitions $\mathrm{step}_r$ and outputs $\mathrm{out}_r$ for each seed $r$. Its output with seed $r$ on the stream $l = (a_1, \dots, a_m)$ is

$$A_r(l) = \mathrm{out}_r\big(\mathrm{step}_r(\cdots \mathrm{step}_r(\mathrm{step}_r(\mathrm{init}_r, a_1), a_2) \cdots, a_m)\big),$$

obtained by reading $l$ from left to right; for the empty stream it is $\mathrm{out}_r(\mathrm{init}_r)$.
