# Odd-cut slack matrix of the perfect matching polytope

Let $n$ be even and let $K_n=(V,E)$ be the complete graph. By Edmonds' theorem the perfect matching polytope $P_{\mathrm{PM}}(n)$ is described by $x \ge 0$, $x(\delta(v))=1$ for $v \in V$, and the odd-cut inequalities $x(\delta(U)) \ge 1$ for $U \subseteq V$ with $|U|$ odd. The odd-cut slack matrix has rows indexed by odd sets $U$ and columns indexed by perfect matchings $M$ of $K_n$:

$$
S_{U,M}=|M \cap \delta(U)|-1 \in \{0,2,4,\dots\}.
$$

It is a submatrix of the slack matrix of $P_{\mathrm{PM}}(n)$ and $\|S\|_\infty \le n$. Its support is covered by $O(n^4)$ rectangles $\{U : e_1,e_2 \in \delta(U)\} \times \{M : e_1,e_2 \in M\}$ over non-adjacent pairs $e_1,e_2$, so rectangle covering bounds alone are polynomial.

## Depends on

- [Perfect matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope.md)
- [Edmonds' perfect matching polytope theorem](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope-eq.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)

## Sources

- Jack Edmonds, "Maximum Matching and a Polyhedron with 0,1-Vertices", Journal of Research of the National Bureau of Standards (1965).
- Mihalis Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences (1991).
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
