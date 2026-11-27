# Nonzero eigenvalues of AB and BA

Let $V$ and $W$ be vector spaces over a field $\mathbb{K}$, of any dimension, let $f : V \to W$ and $g : W \to V$ be linear maps, and let $\mu \in \mathbb{K}$ be nonzero. Then $\mu$ is an eigenvalue of $f \circ g$ if and only if it is an eigenvalue of $g \circ f$.

## Idea

If $fg\,x = \mu x$ with $x \ne 0$ and $\mu \ne 0$, then $y = g x$ satisfies $gf\,y = g(fg\,x) = \mu y$, and $y \ne 0$ because $f y = \mu x \ne 0$. So $g$ carries eigenvectors of $fg$ to eigenvectors of $gf$, and $f$ carries them back. Restricted to the $\mu$-eigenspaces, $g$ and $f/\mu$ are mutually inverse, so the eigenspaces are isomorphic and the geometric multiplicities agree. The eigenvalue $0$ is different: for an $m \times n$ matrix $A$ and an $n \times m$ matrix $B$ with $m < n$, $BA$ always has the eigenvalue $0$ while $AB$ may not. A special case: $T^*T$ and $TT^*$ have the same nonzero eigenvalues; for a matrix $T$ these are the squares of its nonzero singular values.

## Statements

- [Nonzero eigenvalues of fg and gf coincide](has-eigenvalue-comp-iff.md)
- [Nonzero eigenvalues of matrix products AB and BA coincide](has-eigenvalue-mul-iff-3.md): for matrices $AB$ and $BA$
- [Nonzero eigenvalues of fg and gf coincide, for endomorphisms](has-eigenvalue-mul-iff-2.md): for endomorphisms
- [Nonzero eigenvalues of ST and TS coincide](has-eigenvalue-mul-iff.md): for bounded operators on a normed space
- [Nonzero eigenvalues of an operator times its adjoint, in either order](has-eigenvalue-adjoint-mul-self-iff.md): special case: $T^*T$ and $TT^*$
- [Eigenvectors of fg map to eigenvectors of gf](has-eigenvector-comp.md): $g$ carries eigenvectors of $fg$ to eigenvectors of $gf$
- [Eigenvectors of fg map to eigenvectors of gf, for endomorphisms](has-eigenvector-mul.md): the same, for endomorphisms
- [Eigenspace of fg maps into the eigenspace of gf](maps-to-eigenspace-comp.md): $g$ maps the eigenspace of $fg$ into that of $gf$, also for $\mu = 0$
- [Injectivity of g between eigenspaces of fg and gf](injective-restrict-eigenspace-comp.md): injectivity of this restriction
- [Surjectivity of g between eigenspaces of fg and gf](surjective-restrict-eigenspace-comp.md): surjectivity of this restriction
- [Linear equivalence of eigenspaces of fg and gf](eigenspace-comp-equiv.md): a stronger form: the eigenspaces are isomorphic
- [Eigenspaces of fg and gf are equivalent, for endomorphisms](eigenspace-mul-equiv.md): the same, for endomorphisms
- [Geometric multiplicities of fg and gf agree](finrank-eigenspace-comp-eq.md): a stronger form: equal geometric multiplicities
- [Geometric multiplicities of fg and gf agree, for endomorphisms](finrank-eigenspace-mul-eq-2.md): the same, for endomorphisms
- [Geometric multiplicities of matrix products AB and BA agree](finrank-eigenspace-mul-eq-3.md): the same, for matrices
- [Equal geometric multiplicities of nonzero eigenvalues of ST and TS](finrank-eigenspace-mul-eq.md): the same, for bounded operators
