# The TSP polytope has extension complexity 2^Omega(sqrt n)

Let $\mathrm{TSP}(n)$ be the convex hull of the edge characteristic vectors of Hamiltonian cycles of the complete graph $K_n$. For $p \ge 1$ the correlation polytope $\mathrm{COR}(p)$ is a coordinate projection of a face of $\mathrm{TSP}(N)$ for some $N \le 69p^2 + O(1)$, obtained from a directed Hamiltonian-cycle gadget for the correlation equations on $O(p^2)$ vertices by the directed-to-undirected three-split construction. Consequently $\mathrm{xc}(\mathrm{TSP}(n)) \ge (3/2)^{\Omega(\sqrt{n})}$, so no polynomial-size linear program over the edge variables (with extra variables) describes the TSP polytope.

## Proof sketch

Encode $C_{ij} = C_{ii} \wedge C_{jj}$ as a 3-SAT formula, realize its satisfying assignments as directed Hamiltonian cycles of a diamond-and-clause gadget, convert to undirected tours by splitting each vertex into a path of three vertices, and take the face where all non-edges of the gadget have weight zero.

## Depends on

- [The correlation polytope](correlation-polytope.md)
- [Symmetric TSP as a decision problem](../../../TheoryOfComputation/np-completeness/paths-cycles-and-subgraphs/traveling-salesperson-problem/tsp-dec.md)

## Proof depends on

- [Kaibel-Weltge: the correlation polytope has extension complexity at least (3/2)^n](correlation-polytope-lower-bound.md)
- [Faces and projections do not increase extension complexity](extension-complexity-faces-and-projections.md)

## Sources

- S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary and R. de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", Journal of the ACM 62(2), 2015.
- V. Kaibel and S. Weltge, "A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially", Discrete & Computational Geometry 53(2), 2015.
