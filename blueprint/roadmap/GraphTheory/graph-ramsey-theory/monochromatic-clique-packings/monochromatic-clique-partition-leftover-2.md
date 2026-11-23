# Burr–Erdős–Spencer theorem on monochromatic clique packings

For every natural number
$k \ge 2$ there is $n_0$ such that for every $n \ge n_0$ the following holds. Let
$r = R(k, k - 1)$ be the classical two-colour Ramsey number and let
$L = r - 1 + \big((n + 1 - r) \bmod k\big)$, where $n + 1 - r$ is read as $0$ if it is negative.
View a simple graph $G$ on $n$ vertices as a two-colouring of the edges of $K_n$, with the edges
of $G$ red and those of its complement $G^c$ blue. Then every such colouring admits a finite
family of pairwise disjoint sets of vertices, each a $k$-clique of $G$ or of $G^c$, that leaves at
most $L$ vertices uncovered; and some colouring admits no such family leaving fewer than $L$
vertices uncovered.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1015, https://www.erdosproblems.com/1015 (status SOLVED); resolution: S. A. Burr, P. Erdős and J. H. Spencer, Ramsey theorems for multiple copies of graphs, Trans. Amer. Math. Soc. 209 (1975), 87-99, §5, Theorem 6: if k is given, then for sufficiently large n, f(n, k) = r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k), where f(n, k) is the minimal integer such that any two-coloring of K_n admits vertex-disjoint monochromatic K_k with at most f(n, k) points left over; erdosproblems.com/1015 lists the problem as solved citing this paper, https://users.renyi.hu/~p_erdos/1975-35.pdf.
