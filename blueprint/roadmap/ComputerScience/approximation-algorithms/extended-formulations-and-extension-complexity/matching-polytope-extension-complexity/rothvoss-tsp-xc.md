# Rothvoss: the TSP polytope of K_n has extension complexity 2^Omega(n)

Let $P_{\mathrm{TSP}}(n) \subseteq \mathbb{R}^{\binom{n}{2}}$ be the convex hull of the indicator vectors of Hamiltonian cycles of $K_n$. There is an absolute constant $c > 0$ with

$$
\mathrm{xc}(P_{\mathrm{TSP}}(n)) \ge 2^{cn} \qquad \text{for all}\ n \ge 4,
$$

where $\mathrm{xc}$ is extension complexity over $\mathbb{R}$. This improves the earlier, weaker $2^{\Omega(\sqrt{n})}$ bound of Fiorini, Massar, Pokutta, Tiwary and de Wolf; the bound is tight up to the constant in the exponent.

## Proof sketch

Yannakakis constructed, for every even $n'$, a face of $P_{\mathrm{TSP}}(n)$ with $n=O(n')$ and a linear map sending it onto $P_{\mathrm{PM}}(n')$, by replacing vertices with gadgets whose traversals encode matching edges. Since extension complexity does not increase when passing to a face (intersecting with the equations of tight inequalities) or applying an affine map, $\mathrm{xc}(P_{\mathrm{TSP}}(n)) \ge \mathrm{xc}(P_{\mathrm{PM}}(n'))=2^{\Omega(n)}$.

## Depends on

- [Extended formulations and extension complexity](../extended-formulation.md)

## Proof depends on

- [Rothvoss: the perfect matching polytope of K_n has extension complexity 2^Omega(n)](rothvoss-perfect-matching-xc.md)
- [Faces and projections do not increase extension complexity](../extension-complexity-faces-and-projections.md)
- [Faces of a convex polytope](../../../../Combinatorics/polytopes-simplicial-complexes/faces-of-convex-polytopes/faces.md)
- [Perfect matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope.md)

## Sources

- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369, Section 1.1 (Corollary 2).
- Mihalis Yannakakis, "Expressing Combinatorial Optimization Problems by Linear Programs", Journal of Computer and System Sciences (1991).
- Samuel Fiorini, Serge Massar, Sebastian Pokutta, Hans Raj Tiwary, Ronald de Wolf, "Exponential Lower Bounds for Polytopes in Combinatorial Optimization", STOC (2012) and Journal of the ACM (2015), arXiv:1111.0837.
