# The Zeckendorf odometer

The odometer is the map $T$ on digit sequences
$x = (x_k)_{k \in \mathbb{N}}$ with $x_k \in \{0, 1\}$ defined as follows. If $x_k = x_{k+1} = 0$
for some $k \ge 2$, let $k$ be the least such index; then $T(x)_j = 0$ for $j < k$, $T(x)_k = 1$
and $T(x)_j = x_j$ for $j > k$. If there is no such $k$, then $T(x)$ is the zero sequence.

On a Zeckendorf-adic integer, where digit $k \ge 2$ carries the weight of the Fibonacci number
$F_k$, the map $T$ is addition of $1$, and $x + r$ denotes $T^r(x)$ for $r \in \mathbb{N}$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 2.2 (definition of `T`).
