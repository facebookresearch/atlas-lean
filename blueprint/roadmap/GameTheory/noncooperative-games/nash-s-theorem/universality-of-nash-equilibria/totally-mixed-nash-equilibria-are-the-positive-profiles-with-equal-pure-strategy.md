# Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs

Let $G$ be a finite game as above and let $C_i(x; a)$ denote the expected cost to player $i$ of the pure strategy $a \in S_i$ when the other players play the mixed profile $x_{-i}$. A vector $x = (x_i(a))_{i, a}$ is a totally mixed Nash equilibrium of $G$ if and only if

1. $x_i(a) > 0$ for all $i$ and $a \in S_i$,
2. $\sum_{a \in S_i} x_i(a) = 1$ for every $i$, and
3. for every player $i$ and all $a, b \in S_i$, $C_i(x; a) = C_i(x; b)$.

## Proof sketch

In a mixed Nash equilibrium every pure strategy in the support of $x_i$ is a best response, so all strategies in the support have the minimal expected cost. When the support is all of $S_i$ the costs are equal; conversely equal costs make every pure strategy, hence every mixture, a best response.

## Depends on

- [Totally mixed Nash equilibrium](totally-mixed-nash-equilibrium.md)

## Proof depends on

- [Support characterization of mixed best responses](../support-characterization-of-mixed-best-responses.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
