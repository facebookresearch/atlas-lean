# Stability hierarchy for fixed points of diploid selection

Consider one locus with $n$ alleles in a randomly mating diploid population. Let $A \in \mathbb{R}^{n\times n}$ be a symmetric fitness matrix with positive entries, $A_{ij}$ the fitness of genotype $ij$, and let $\mathbf{x} \in \Delta_n$ be the vector of allele frequencies. Selection acts by the map $f : \Delta_n \to \Delta_n$,

$$
x_i' = f_i(\mathbf{x}) = x_i\,\frac{(A\mathbf{x})_i}{\mathbf{x}^{\top}A\mathbf{x}}, \qquad i = 1,\dots,n,
$$

a discrete replicator dynamics for the symmetric coordination game $(A,A)$, whose potential is the mean fitness $\pi(\mathbf{x}) = \mathbf{x}^{\top}A\mathbf{x}$.

- $\mathbf{x}$ is a fixed point of $f$ iff $(A\mathbf{x})_i = \mathbf{x}^{\top}A\mathbf{x}$ for every $i$ with $x_i > 0$.
- A fixed point is **linearly stable** if every eigenvalue of the Jacobian of $f$ at it has modulus at most $1$.
- A strategy $\mathbf{x}$ is **(strict) Nash stable** if it is a (strict) symmetric Nash equilibrium of $(A,A)$ and the matrix $T(A,\mathbf{x})$ obtained by restricting $A$ to the support of $\mathbf{x}$ and projecting onto the tangent space of the face is negative (definite) semidefinite.

**Theorem.** For every symmetric $A$,

$$
\text{strict Nash stable} \subseteq \text{asymptotically stable} \subseteq \text{stable} \subseteq \text{Nash stable} = \text{linearly stable},
$$

where a fixed point is stable iff it is a local maximum of $\pi$ on $\Delta_n$ and asymptotically stable iff it is a strict local maximum. Moreover, the set of initial frequencies in $\Delta_n$ from which $f$ converges to a linearly unstable fixed point has Lebesgue measure zero.

So, for almost every starting population, the long-run allele frequencies are a linearly stable (equivalently Nash stable) fixed point, and genetic diversity survives exactly when such a fixed point has support of size at least two and attracts a positive-measure set.

## Expansion

The characterization of stable fixed points as local maxima of mean fitness is the Baum–Eagon / Lyubich fundamental theorem for this dynamics: $\pi$ strictly increases along non-fixed orbits. Nash stability is the first- and second-order optimality condition for $\pi$ on the simplex, so it coincides with linear stability. The measure-zero statement uses the center-stable manifold theorem: near a linearly unstable fixed point the points that never leave a neighbourhood lie on a lower-dimensional manifold, and since $f$ is a local diffeomorphism on the interior, countably many preimages of null sets remain null.

## Sources

- Ruta Mehta, Ioannis Panageas, Georgios Piliouras, Sadra Yazdanbod, "The Complexity of Genetic Diversity", in *24th Annual European Symposium on Algorithms (ESA 2016)*, LIPIcs 57 (2016), 65:1–65:17, <https://doi.org/10.4230/LIPIcs.ESA.2016.65>; preprint arXiv:1411.6322, <https://doi.org/10.48550/arXiv.1411.6322>. Numbering of arXiv v2: Section 4 (Theorem 4.7, Definition 4.9, Theorem 4.10), Section 5 (Definition 5.1, Lemmas 5.3–5.5, Theorem 5.6).
