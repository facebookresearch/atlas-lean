# Recurrence for the principal-node count

For a branching factor $k \ge 1$ and a height $d$, the Knuth–Moore principal-node count $P(k, d) = k^{\lceil d/2 \rceil} + k^{\lfloor d/2 \rfloor} - 1$ satisfies
$$P(k, d + 1) = P(k, d) + (k - 1)\, k^{\lfloor d/2 \rfloor}.$$
