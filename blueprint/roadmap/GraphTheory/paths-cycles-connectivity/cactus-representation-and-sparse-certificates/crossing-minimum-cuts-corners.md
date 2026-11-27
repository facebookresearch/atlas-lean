# Corner structure of two crossing minimum cuts

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and edge connectivity $\lambda > 0$, and let $S, T$ be crossing global minimum cuts with corners $A = S \cap T$, $B = S \setminus T$, $C = T \setminus S$, $D = V \setminus (S \cup T)$. Then each of $A, B, C, D$ is a side of a global minimum cut, there are no diagonal edges,

$$
w(A, D) = w(B, C) = 0,
$$

and each of the four cyclically adjacent pairs carries exactly half the connectivity:

$$
w(A, B) = w(B, D) = w(D, C) = w(C, A) = \lambda / 2 .
$$

## Proof sketch

For the cut function $f(X) = w(\partial X)$ one has the identity $f(S \cap T) + f(S \cup T) = f(S) + f(T) - 2w(B, C)$, and similarly $f(S \setminus T) + f(T \setminus S) = f(S) + f(T) - 2w(A, D)$. All four corners are nonempty proper subsets, so each term on the left is at least $\lambda$ while the right sides are at most $2\lambda$; hence all corners are minimum cut sides and both diagonals vanish. With no diagonal edges, $f(A) = w(A,B) + w(A,C) = \lambda$, $f(B) = w(A,B) + w(B,D) = \lambda$, $f(C) = w(A,C) + w(C,D) = \lambda$ and $f(S) = w(A, C) + w(B, D) = \lambda$, and solving this linear system gives all four values equal to $\lambda/2$.

## Depends on

- [Crossing pairs of vertex bipartitions](crossing-vertex-bipartitions.md)
- [Steiner minimum cuts of a terminal set](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)

## Proof depends on

- [Submodular set function](../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Efim A. Dinits, Alexander V. Karzanov, Michael V. Lomonosov, "On the Structure of a System of Minimum Edge Cuts of a Graph", Studies in Discrete Optimization (1976).
