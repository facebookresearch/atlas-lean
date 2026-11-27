# Oppenheim's trickling-down theorem for spectral gaps

Let $X$ be a pure weighted complex of dimension $d \ge 2$ whose $1$-skeleton is connected. Suppose that for every vertex $v \in X(0)$ the underlying graph of the link $X_v$ is connected with $\lambda_2(M_v) \le \lambda$, where $0 \le \lambda < 1/2$. Then the $1$-skeleton walk $M$ of $X$ satisfies

$$
\lambda_2(M) \le \frac{\lambda}{1 - \lambda}.
$$

Consequently, if the links of all $(d-2)$-faces have second eigenvalue at most $\lambda_{d-2}$ and all intermediate links are connected, then by induction downward every link of an $i$-face has second eigenvalue at most $\lambda_i$, where $\lambda_{i-1} = \lambda_i / (1 - \lambda_i)$. In particular, $\lambda_{d-2} \le \lambda/(1 + (d-1)\lambda)$ implies that $X$ is a one-sided $\lambda$-local spectral expander.

## Proof sketch

Take an eigenfunction $f$ of $M$ with eigenvalue $\mu$, orthogonal to constants. Applying Garland's localization to $\langle Mf, f\rangle$ and splitting each restriction $f_v$ into its link-constant part and its link-orthogonal part, the link hypothesis bounds the orthogonal contribution by $\lambda$, while the constant parts reassemble to $\langle M f, M f \rangle = \mu^2 \langle f, f\rangle$. This yields $\mu \le \lambda + (1 - \lambda)\mu^2$-type inequality; since $M$ is connected the root $\mu \le \lambda/(1-\lambda)$ follows. Iterating over links gives the dimension-wise recursion.

## Depends on

- [Local spectral expanders (one-sided and two-sided)](local-spectral-expander.md)
- [Link of a face in a weighted complex](link-of-face.md)
- [Pure weighted simplicial complexes and their face distributions](pure-weighted-complex.md)

## Proof depends on

- [Garland's method: localization of the link Laplacian quadratic form](garland-method.md)

## Sources

- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
