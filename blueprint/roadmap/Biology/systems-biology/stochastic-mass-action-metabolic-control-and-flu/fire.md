# State after one reaction firing

Let $N$ be a [chemical reaction network](../complex-balancing-and-the-deficiency-zero-theore/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$. For a reaction $r$ and a state $x \in \mathbb{N}^S$ (molecule counts), the state after
one firing of $r$ is $x - \mathrm{src}(r) + \mathrm{prod}(r)$, computed coordinatewise with natural-number
subtraction truncated at $0$. It is meaningful when $\mathrm{src}(r) \le x$, the only case in which the
[propensity](propensity.md) can be nonzero.
