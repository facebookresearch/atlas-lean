# Garland's method: localization of the link Laplacian quadratic form

Let $X$ be a pure weighted complex of dimension $d \ge 2$ and let $f : X(0) \to \mathbb{R}$. For a vertex $v$ write $f_v$ for the restriction of $f$ to the link $X_v$. Then the global quantities of the $1$-skeleton random walk $M$ decompose as averages of link quantities:

$$
\langle f, f \rangle = \mathbb{E}_{v \sim \Pi_0} \langle f_v, f_v \rangle_{v}, \qquad \langle M f, f \rangle = \mathbb{E}_{v \sim \Pi_0} \langle M_v f_v, f_v \rangle_{v},
$$

where $\langle \cdot, \cdot \rangle_v$ is the inner product weighted by the vertex distribution of $X_v$. In particular, every eigen-bound on the links transfers to a bound on the Rayleigh quotient of $M$ restricted to suitable functions.

## Proof sketch

Both identities follow by expanding each side as a sum over edges $\{u,w\} \in X(1)$ (respectively vertices) and noticing that sampling a vertex $v \sim \Pi_0$ and then an edge of $X_v$ is the same as sampling a triangle and one of its edges, with the triangle distribution induced by $\Pi_d$. The bookkeeping uses only the downward definition of the face distributions.

## Depends on

- [Link of a face in a weighted complex](link-of-face.md)
- [Pure weighted simplicial complexes and their face distributions](pure-weighted-complex.md)

## Sources

- H. Garland, "p-adic curvature and the cohomology of discrete subgroups of p-adic groups", Annals of Mathematics 97 (1973) 375-423.
- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
