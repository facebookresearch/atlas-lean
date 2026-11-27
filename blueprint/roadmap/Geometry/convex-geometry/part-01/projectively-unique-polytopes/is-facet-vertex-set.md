# Facets of a polytope given by its vertices

Let $d \ge 1$ and let $V \subseteq \mathbb{R}^d$ be the [vertex set of a $d$-polytope](is-polytope-vertex-set.md). A set $F \subseteq V$ is the vertex set of a facet of the polytope when $F$ is nonempty and there are a nonzero linear functional $\ell : \mathbb{R}^d \to \mathbb{R}$ and $c \in \mathbb{R}$ with $\ell(v) \le c$ for all $v \in V$ and

$$F = \{v \in V : \ell(v) = c\},$$

so that $\ell$ attains its maximum $c$ over $V$ exactly on $F$, and the direction of the affine span of $F$ (the span of the differences of its points) has dimension $d - 1$. For $d = 0$ there are no facets.

The nonemptiness, that is the attainment of the bound, is essential: without it the empty set would pass for a facet of the segment ($V = \{0, 1\} \subseteq \mathbb{R}$, $\ell(x) = x$, $c = 2$), since the direction of the empty affine span is zero.

## Depends on

- [Vertex sets of $d$-polytopes](is-polytope-vertex-set.md)

## Sources

- G. M. Ziegler, *Lectures on Polytopes*, Graduate Texts in Mathematics 152, Springer, 1995, §2.1 (faces and facets of a polytope)
