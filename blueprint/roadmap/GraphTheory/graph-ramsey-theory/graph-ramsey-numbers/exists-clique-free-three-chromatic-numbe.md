# Chromatic number of Kim's triangle-free graphs

Every sufficiently large $n$ has a triangle-free graph $G$ on $n$ vertices with

$$\chi(G) \ge \tfrac19 \sqrt{n / \log n},$$

which follows from [Kim's bound on the independence number](exists-clique-free-three-indep-num-le.md) and $\chi(G) \ge n / \alpha(G)$. With the upper bound on $R(3,t)$ it determines the maximum chromatic number of triangle-free graphs on $n$ vertices up to a constant factor: between $(1 - o(1)) \frac19 \sqrt{n/\log n}$ and $(1 + o(1)) 2\sqrt2 \sqrt{n/\log n}$.

## Informally uses

- [Kim's triangle-free graphs with small independence number](exists-clique-free-three-indep-num-le.md): the same graphs, with $\chi(G) \ge n / \alpha(G)$.

## Sources

- J. H. Kim, "The Ramsey number R(3,t) has order of magnitude t²/log t", *Random Structures & Algorithms* 7 (1995), 173–207, Corollary 1.2 and the discussion after it.
