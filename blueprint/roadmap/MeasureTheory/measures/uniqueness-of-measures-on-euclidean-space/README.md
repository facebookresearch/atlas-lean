# Uniqueness of measures on R^d from their values on boxes

Let $\mu_1$ and $\mu_2$ be finite measures on $\mathbb{R}^d$. If
$\mu_1((a, b]) = \mu_2((a, b])$ for all boxes $(a, b] = \prod_{i=1}^d (a_i, b_i]$ with $a_i \le b_i$
for every $i$, then $\mu_1 = \mu_2$. Some finiteness is needed: for $d \ge 1$, counting measure and
twice counting measure agree on every box but differ; finiteness on every box would be enough.

## Idea

Boxes form a $\pi$-system, closed under finite intersections, that generates the Borel
$\sigma$-algebra. By Dynkin's $\pi$-$\lambda$ theorem, the sets on which two finite measures with the
same total mass agree form a $\lambda$-system, so it contains the whole $\sigma$-algebra; the total
masses agree because $\mathbb{R}^d$ is an increasing union of boxes. The variants derive the
multivariate form of "a distribution function determines a probability measure", with lower
orthants in place of boxes, and the uniqueness half of the construction of measures from
distribution functions by inclusion–exclusion over the vertices of a box.

## Statements

- [Rectangle uniqueness for measures on $\mathbb{R}^d$](eq-of-forall-ioc-eq.md)
- [Uniqueness from rectangle values](eq-of-forall-rectangle-value-eq.md): a variant with the values given by a distribution function.
- [Quadrant uniqueness for measures on $\mathbb{R}^d$](ext-of-iic-pi.md): a variant with lower orthants.
- [Nonempty bounded half-open intervals](c-ioc-pi.md): the generating class in one dimension.
- [Nonempty bounded half-open intervals form a π-system](is-pi-system-c-ioc-pi.md): used in the proof.
- [Half-open intervals countably span $\mathbb{R}$](is-countably-spanning-c-ioc-pi.md): used in the proof.
- [Half-open intervals generate the Borel σ-algebra on $\mathbb{R}$](generate-from-c-ioc-pi.md): used in the proof.
- [Lower orthants generate the product σ-algebra on $\mathbb{R}^d$](generate-from-pi-iic.md): used for the orthant variant.
- [Lower orthants form a π-system](is-pi-system-pi-iic.md): used for the orthant variant.
- [Rectangle value of a function](rectangle-value.md): a definition used in the rectangle-value variant.
- [Vertex of a rectangle](rectangle-vertex.md): a definition used in the rectangle-value variant.
