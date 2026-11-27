# Heilmann-Lieb theorem: real roots of the matching polynomial

For every graph $G$ of maximum degree $\Delta \ge 2$, the matching polynomial $\mu_G$ is real-rooted and all of its roots lie in $[-2\sqrt{\Delta - 1},\ 2\sqrt{\Delta - 1}]$.

## Proof sketch

By Godsil's path-tree construction, $\mu_G$ divides the characteristic polynomial of the path tree $T(G, v)$, a tree of maximum degree $\Delta$, and for trees the matching polynomial equals the characteristic polynomial, hence is real-rooted. The spectral radius of a tree of maximum degree $\Delta$ is at most $2\sqrt{\Delta - 1}$, as it is a finite subtree of the infinite $(\Delta)$-regular tree whose spectral radius is $2\sqrt{\Delta-1}$.

## Depends on

- [The matching polynomial of a graph](matching-polynomial-of-a-graph.md)
- [Real-rooted polynomials](../../../Algebra/zeros-of-polynomials/real-rooted-polynomials/is-real-rooted.md)

## Sources

- Ole J. Heilmann, Elliott H. Lieb, "Theory of monomer-dimer systems", Communications in Mathematical Physics 25 (1972).
- Chris D. Godsil, Ivan Gutman, "On the matching polynomial of a graph", Algebraic Methods in Graph Theory, Colloquia Mathematica Societatis Janos Bolyai 25 (1981).
