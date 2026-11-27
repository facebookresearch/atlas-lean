# Total positivity

A real matrix is totally nonnegative (totally positive) if all its minors are nonnegative (positive). Fomin and Zelevinsky's account (*Total positivity: tests and parametrizations*, Math. Intelligencer 22 (2000), arXiv:math/9912128v1) starts from planar networks: by Lindström's lemma every minor of the weight matrix of a planar network is a sum of weights of families of vertex-disjoint paths, so nonnegative weights give a totally nonnegative matrix (Corollary 2) and positive weights on a totally connected network give a totally positive one (Corollary 3); conversely every totally positive matrix arises this way (Theorem 5), which yields the test by $n^2$ initial minors (Theorem 9, due to Gasca and Peña). Here the two corollaries follow from a weighted Lindström–Gessel–Viennot lemma; the pages also compare nonnegative minors of rectangular matrices with total nonnegativity of square matrices, and state the initial-minor test.

- [Totally positive matrices](totally-positive-matrices/README.md)
- [Total positivity of hyper-Fibonacci Toeplitz matrices](hyper-fibonacci-toeplitz-matrices/README.md)
- [Total nonnegativity of planar networks](planar-networks/README.md)
- [Symmetrized product of principal minors over set partitions](symmetrized-fischer-product.md)
- [AimPL total positivity Problem 1.55 (converse of the Barrett–Johnson inequalities)](barrett-johnson-converse.md)
- [Converse of the Barrett–Johnson inequalities for totally nonnegative matrices](barrett-johnson-converse-holds.md)
- [Path tracing for triangular systems](path-tracing-for-triangular-systems/README.md)

## Related topics

- [Lindström–Gessel–Viennot lemma](../../../Combinatorics/catalan-numbers-lattice-paths/dyck-paths-lattice-walks/lindstrom-gessel-viennot-weighted.md): the determinant identity behind the positivity of minors of planar networks.
- [Cluster algebras](../../../RingTheory/cluster-algebras/README.md): introduced by Fomin and Zelevinsky as an algebraic framework for total positivity; for example the flag minors of $SL_3$ satisfy the exchange relation $P_2 P_{13} = P_1 P_{23} + P_3 P_{12}$ (Fomin, Williams and Zelevinsky, arXiv:1608.05735v5, Example 3.2.1).
- [Standard Young tableaux and the hook length formula](../../../Combinatorics/symmetric-functions-q-analogues/standard-young-tableaux-and-the-hook-length-form/README.md): the Robinson–Schensted–Knuth correspondence and Stanley's enumeration of tableaux; Jacobi–Trudi determinants for Schur functions are a classical application of Lindström–Gessel–Viennot.
- [Lorentzian polynomials](../../../Combinatorics/matroid-theory/lorentzian-polynomials/README.md): Brändén and Huh's positivity theory for polynomials, a different notion of positivity with log-concavity consequences.
- [Tropical varieties](../../../AlgebraicGeometry/varieties-and-projective-geometry/tropical-varieties/README.md): tropical geometry in the sense of Maclagan and Sturmfels; the tropicalisation of the totally positive part of a Grassmannian is a further meeting point of total positivity and tropical geometry.
