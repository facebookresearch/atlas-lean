# Best response polytopes of a bimatrix game

Let $(A, B)$ be a bimatrix game with row set $M$ and column set $N$. Its *best response polytopes* are

$$
P = \{x \in \mathbb{R}^M : x \ge 0,\ B^\top x \le \mathbf 1\}, \qquad Q = \{y \in \mathbb{R}^N : A y \le \mathbf 1,\ y \ge 0\}.
$$

Constraints are labelled by $M \sqcup N$: a point $x \in P$ has label $i \in M$ if $x_i = 0$ and label $j \in N$ if $(B^\top x)_j = 1$; a point $y \in Q$ has label $i \in M$ if $(Ay)_i = 1$ and label $j \in N$ if $y_j = 0$. A pair $(x, y) \in P \times Q$ is *completely labelled* if every label in $M \sqcup N$ is a label of $x$ or of $y$.

## Depends on

- [Nash equilibrium of a bimatrix game](../is-bimatrix-nash.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
