# State before one reaction firing

Let $N$ be a [chemical reaction network](../complex-balancing-and-the-deficiency-zero-theore/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$. For a reaction $r$ and a state $x \in \mathbb{N}^S$, the state from which one firing of $r$
leads to $x$ is $x - \mathrm{prod}(r) + \mathrm{src}(r)$, computed coordinatewise with natural-number
subtraction truncated at $0$. It is meaningful when $\mathrm{prod}(r) \le x$.
