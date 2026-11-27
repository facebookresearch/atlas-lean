# Necessary capacity inequalities for higher-dimensional ball packing

Fix integers $n\ge3$, $k\ge1$, a real $R>0$ and $r_i>0$ for $i=1,\dots,k$. In $\mathbb C^n$ use the standard form $\omega(v,w)=\sum_j(\Re v_j\Im w_j-\Im v_j\Re w_j)$ and capacity $\pi\sum_j|z_j|^2$. A packing is given by smooth topological embeddings defined on open neighborhoods of each closed capacity-$r_i$ ball, with derivative pulling back $\omega$ to itself throughout those neighborhoods. Their closed-ball images are disjoint for every pair of distinct indices and lie inside the open capacity-$R$ ball.

If a packing exists, then $\sum_i r_i^n<R^n$ and $r_i+r_j<R$ for every distinct $i,j$. In particular, neither inequality is weak, and the pairwise condition is vacuous for a single source ball.

## Depends on

- Standard symplectic form, smooth neighbourhood embeddings of closed balls and capacity normalization.

## Proof depends on

- Volume preservation with a strict margin and pairwise capacity obstruction for two disjoint source balls.

## Expansion

Establish strictness using the entire closed images inside the open target. Keep the pairwise obstruction separate from volume (the latter alone does not bound each pairwise sum).

## Sources

- OpenAI Math, [`packing_necessity`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BallPackingNecessity.lean#L38-L42) (statement and local definitions).
