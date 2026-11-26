# Factorization of minimal polynomial folding maps of the simplex

A $d$-folding map $f:\Delta^n\to\Delta^n$ is a continuous, onto map that is $d$-to-$1$ on the interior of the image simplex, so that $\Delta^n$ splits into $d$ pieces each mapped bijectively onto $\Delta^n$. On $\Delta^1=[0,1]$ the Chebyshev maps

$$
f_k(x)=\frac{1-T_k(1-2x)}{2},\qquad T_k(x)=\cos(k\arccos x),
$$

are $k$-folding maps of degree $k$; $f_2(x)=4x(1-x)$ is the logistic map at full chaos.

Two maps are face-constrained homotopic if they are connected by a pair of deformations $(K(\cdot,t),H(\cdot,t))$, with each $K(\cdot,t)$ a bijection of $\Delta^n$, that keep every point $x$ in the face containing $x$ and its image in the face containing $f(x)$. A polynomial folding map of degree $k$ (an element of the space of polynomial maps of the simplex) is **minimal** if no face-constrained homotopic map of lower degree maps $\Delta^n$ into itself.

Write $f=(P_1,\dots,P_n)$ and $P_{n+1}=1-\sum_jP_j$. The preimage of the facet $\{y_i=0\}$ splits into an interior part $z_i$ and a boundary part $b_i\subset\partial\Delta^n$; since $b_i$ is the zero set of a polynomial on the boundary, it is empty or a union of whole facets.

**Theorem.** Let $f$ be a minimal polynomial folding map of degree $k$. Then each $P_i$, $1\le i\le n+1$, factors as

$$
P_i(x)=l_i(x)\,q_i(x)^2\,m_i(x),
$$

where

- the zero locus of $l_i$ in $\Delta^n$ is exactly $b_i$, $\deg l_i$ equals the number of facets in $b_i$, and $\prod_{i=1}^{n+1}l_i(x)=\big(1-\sum_jx_j\big)\prod_{i=1}^nx_i$;
- the zero locus of $q_i$ in the interior of $\Delta^n$ is exactly $z_i$;
- $l_i$ and $m_i$ are strictly positive in the interior of $\Delta^n$, and the zero set of $m_i$ is empty or contained in that of $l_i$;
- $\deg l_i+2\deg q_i+\deg m_i\le k$.

Every folding map sends $\partial\Delta^n$ into $\partial\Delta^n$. Folding maps that send different parts of one facet to different facets have no face-constrained homotopic polynomial representative.

## Depends on

- [Space of bounded-degree polynomial maps of the simplex is compact and convex](space-of-bounded-degree-polynomial-maps-of-the-simplex-is-compact-and-convex.md)

## Expansion

$P_i\ge0$ on $\Delta^n$, so an interior zero of $P_i$ on the fold set $z_i$ must have even order, giving the square $q_i^2$; boundary zeros occur along whole facets, each contributing one linear factor $x_j$ or $1-\sum_jx_j$. Because each facet of the source simplex maps into exactly one facet of the image, each linear factor appears in exactly one $l_i$, giving the product identity. Minimality of the degree makes $l_i=\prod_{j\in b_i}x_j$ the lowest-degree polynomial vanishing on those facets; since the zero set of $P_i$ is already accounted for by $l_i$ and $q_i$, the remaining factor $m_i$ is nonnegative of degree at most $k-\deg l_i-2\deg q_i$, with zeros only inside those of $l_i$.

## Sources

- Sergio Lukic, *A note on the space of evolutionary operators in population genetics and folding dynamics*, arXiv:1305.0151 (2013), Definition 1 and Theorem 2 (Section 3), Lemma 2 (Appendix). <https://doi.org/10.48550/arXiv.1305.0151>
