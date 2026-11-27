# Replicable approximate medians over finite ordered domains

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Let $X$ be a well-ordered domain of size $2^d$ and call $x$ a $\tau$-approximate median of $D$ if $\Pr_{x' \sim D}[x' \le x] \ge \tfrac12 - \tau$ and $\Pr_{x' \sim D}[x' \ge x] \ge \tfrac12 - \tau$. There is a $\rho$-replicable algorithm that outputs a $\tau$-approximate median with probability at least $1 - \rho/2$ using

$$
\tilde O\!\left(\frac{1}{\tau^2 \rho^2} \cdot \Big(\frac{3}{\tau^2}\Big)^{\log^* |X|}\right)
$$

samples. Replicable approximate medians are the key subroutine for replicable learning of halfspaces with margin.

## Proof sketch

Recursively reduce the domain: replicably locate the median of the distribution of the leading bits of samples using a domain of size $\log |X|$, then recurse inside the identified prefix; the recursion depth is $\log^* |X|$, and each level loses a factor $O(1/\tau^2)$ in samples and a constant factor in accuracy. Replicability of each level comes from randomized rounding of empirical quantiles with shared offsets.

## Proof depends on

- [Replicable simulation of a statistical query by randomized rounding](replicable-statistical-query-simulation.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430.
