# Polynomial-time computability of the weighted Lovasz theta function

There is an algorithm that, given a finite simple graph $G$ on $n$ vertices, a weight vector $w \in \mathbb{Z}_{\ge 0}^{V}$ and a rational $\varepsilon > 0$, computes a rational number within $\varepsilon$ of

$$
\vartheta(G, w) = \max\{ w^\top x : x \in \mathrm{TH}(G) \}
$$

in time polynomial in $n$, the encoding length of $w$ and $\log(1/\varepsilon)$. For $w = \mathbf{1}$ this is the Lovasz number $\vartheta(G)$.

## Proof sketch

The theta body $\mathrm{TH}(G)$ lies in $[0, 1]^V$ and contains the indicator vectors of all stable sets, hence the ball of radius $1/(2n)$ around $\frac{1}{2n}\mathbf{1}$, so it is a centered convex body with explicit parameters. Weak membership in $\mathrm{TH}(G)$ reduces to testing approximate positive semidefiniteness of an explicit matrix built from the query through the orthogonal-labeling description, which is done by Gaussian elimination in rational arithmetic. Weak optimization over $\mathrm{TH}(G)$ then follows from the weak-membership-to-optimization theorem, and the coordinate-sum characterization identifies the value with $\vartheta$.

## Depends on

- [Lovász theta function](../theta-function-of-a-graph/lovasz-theta.md)
- [Theta body](../theta-function-of-a-graph/th.md)

## Proof depends on

- [Weak membership yields weak optimization for centered convex bodies](weak-membership-yields-weak-optimization.md)
- [Theta is the maximum of the coordinate sum over the theta body](../theta-function-of-a-graph/lovasz-theta-eq-s-sup-th.md)
- [Well-described polyhedra, centered convex bodies and the strong and weak oracle problems](well-described-polyhedra-and-oracle-problems.md)
- [Orthogonal labeling of a graph](../theta-function-of-a-graph/is-orthogonal-labeling.md)
- [Stable sets lie in the theta body](../theta-function-of-a-graph/char-vec-mem-th.md)

## Sources

- M. Grotschel, L. Lovasz, A. Schrijver, "The ellipsoid method and its consequences in combinatorial optimization", Combinatorica 1 (1981).
- M. Grotschel, L. Lovasz, A. Schrijver, "Polynomial algorithms for perfect graphs", Annals of Discrete Mathematics 21 (1984).
- M. Grotschel, L. Lovasz, A. Schrijver, "Geometric Algorithms and Combinatorial Optimization", Springer (1988).
- D. E. Knuth, "The Sandwich Theorem", Electronic Journal of Combinatorics 1 (1994), arXiv:math/9312214, Section 37 (citing GLS Section 9.3).
- L. Lovász, "Geometric representations of graphs" (2016 course notes), Chapter 6, Section 6.3.4 (Proposition 6.3.5) and Section 6.4.2 (Theorem 6.4.4 and weighted extension).
- A. Gupta, CMU 15-859E Lecture 11 (Fall 2011), Theorem 11.10; R. O'Donnell, CMU 15-859E Lecture 10, Theorem 10.10 (rational Gaussian-elimination PSD test).
