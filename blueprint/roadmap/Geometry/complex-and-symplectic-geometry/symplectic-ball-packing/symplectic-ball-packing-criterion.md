# Equivalence of higher-dimensional symplectic ball packing and the capacity inequalities

Fix integers $n\ge3$, $k\ge1$, a real $R>0$ and $r_i>0$ for $i=1,\dots,k$. In $\mathbb C^n$ use the standard form $\omega(v,w)=\sum_j(\Re v_j\Im w_j-\Im v_j\Re w_j)$ and capacity $\pi\sum_j|z_j|^2$. A packing is given by smooth topological embeddings defined on open neighborhoods of each closed capacity-$r_i$ ball, with derivative pulling back $\omega$ to itself throughout those neighborhoods. Their closed-ball images are disjoint for every pair of distinct indices and lie inside the open capacity-$R$ ball.

A packing exists **if and only if** $\sum_i r_i^n<R^n$ and $r_i+r_j<R$ for every distinct $i,j$. Necessity and sufficiency both use embeddings on neighborhoods, not just maps of open balls.

## Depends on

- Standard symplectic balls and neighborhood-wise symplectic embeddings.

## Proof depends on

- [Necessary inequalities](symplectic-ball-packing-necessary-inequalities.md)
- Construct a packing of neighborhoods under both strict inequalities.

## Expansion

Use exactly the same capacity and closed-image model in both directions; give the construction separately from necessity.

## Sources

- OpenAI Math, [`main_theorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BallPacking.lean#L36-L40) (statement and local definitions).
