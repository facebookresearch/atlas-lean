# Generalized eigenspaces of AB and BA

Let $V$ and $W$ be vector spaces over a field $\mathbb{K}$, of any dimension, let $f : V \to W$ and $g : W \to V$ be linear maps, let $\mu \in \mathbb{K}$ be nonzero, and let $k \in \mathbb{N} \cup \{\infty\}$. The generalized $\mu$-eigenspace of exponent $k$ of an endomorphism $T$ is $\ker (T - \mu)^k$ for finite $k$, and the union of these kernels for $k = \infty$. Then the generalized $\mu$-eigenspaces of exponent $k$ of $f \circ g$ and of $g \circ f$ have the same dimension, where an infinite-dimensional space is given dimension $0$.

## Idea

The map $g$ intertwines the two products, $g \circ (f \circ g) = (g \circ f) \circ g$, so it maps each generalized eigenspace of $fg$ into the corresponding one of $gf$. For $\mu \ne 0$ it is injective there: a vector killed by $g$ is killed by $fg$, and $fg - \mu$ is invertible on such vectors. By symmetry $f$ is injective in the other direction, so the two spaces have the same dimension; in particular they are finite-dimensional together, so the convention for infinite dimension never pairs a finite dimension with an infinite one. For finite-dimensional spaces and $k = \infty$ this says that $AB$ and $BA$ have the same nonzero eigenvalues with the same algebraic multiplicities, which is also visible from the identity $x^n \chi_{AB}(x) = x^m \chi_{BA}(x)$ for an $m \times n$ matrix $A$ and an $n \times m$ matrix $B$.

## Statements

- [Generalized eigenspaces of fg and gf have equal dimension](finrank-gen-eigenspace-comp-eq.md)
- [Generalized eigenspaces of AB and BA have equal dimension](finrank-gen-eigenspace-mul-eq-3.md): for matrices $AB$ and $BA$
- [Generalized eigenspace dimensions agree, for endomorphisms](finrank-gen-eigenspace-mul-eq-2.md): for endomorphisms
- [Equal dimensions of generalized eigenspaces of ST and TS](finrank-gen-eigenspace-mul-eq.md): for bounded operators on a normed space
- [Generalized eigenspaces of fg and gf are finite-dimensional together](finite-gen-eigenspace-comp-iff.md): the generalized eigenspaces are finite-dimensional together
- [Generalized eigenspaces finite-dimensional together, for endomorphisms](finite-gen-eigenspace-mul-iff-2.md): the same, for endomorphisms
- [Generalized eigenspaces of AB and BA are finite-dimensional together](finite-gen-eigenspace-mul-iff-3.md): the same, for matrices
- [Finite-dimensionality of generalized eigenspaces of ST and TS](finite-gen-eigenspace-mul-iff.md): the same, for bounded operators
- [Generalized eigenspace of fg maps into that of gf](maps-to-gen-eigenspace-comp.md): $g$ maps generalized eigenspaces of $fg$ into those of $gf$
- [Restriction of g to generalized eigenspaces of fg and gf](gen-eigenspace-comp-map.md): the restriction of $g$ used in the proof
- [Injectivity of g on generalized eigenspaces of fg](injective-gen-eigenspace-comp-map.md): this restriction is injective for $\mu \ne 0$
- [Kernel of g meets a generalized eigenspace of fg trivially](eq-zero-of-apply-eq-zero-of-mem-gen-eige.md): used for injectivity: the kernel of $g$ meets the generalized eigenspace trivially
