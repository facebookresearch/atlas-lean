# The expected characteristic polynomial of a random signing is the matching polynomial

For every graph $G$, if $s$ is a uniformly random signing then

$$
\mathbb{E}_s\big[\det(xI - A_s)\big] = \mu_G(x) .
$$

## Proof sketch

Expand the determinant as a sum over permutations, each a product of cycles in $G$ with signs. Any permutation containing a cycle of length at least $3$ contributes a product of independent random signs with mean zero; only permutations made of fixed points and transpositions (edges, contributing $s_e^2 = 1$) survive, giving $\sum_i (-1)^i m_i x^{N - 2i}$.

## Depends on

- [The matching polynomial of a graph](matching-polynomial-of-a-graph.md)
- [Two-lifts and signings of a graph](two-lifts-and-signings-of-graphs.md)

## Sources

- Chris D. Godsil, Ivan Gutman, "On the matching polynomial of a graph", Algebraic Methods in Graph Theory, Colloquia Mathematica Societatis Janos Bolyai 25 (1981).
- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Interlacing families I: bipartite Ramanujan graphs of all degrees", Annals of Mathematics 182(1) (2015); arXiv:1304.4132.
