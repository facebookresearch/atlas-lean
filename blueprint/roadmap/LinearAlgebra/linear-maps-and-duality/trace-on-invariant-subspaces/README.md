# Trace is additive over an invariant subspace

Let $V$ be a finite-dimensional vector space over a field $K$, let $e$ be an endomorphism of $V$ and let $W$ be a subspace with $e(W) \subseteq W$. Then $\operatorname{tr}(e) = \operatorname{tr}(e|_W) + \operatorname{tr}(\bar e)$, where $e|_W$ is the restriction of $e$ to $W$ and $\bar e$ the endomorphism of $V/W$ induced by $e$.

## Idea

Choose a basis of $W$ and extend it to a basis of $V$. In that basis the matrix of $e$ is block upper triangular: the top-left block is the matrix of $e|_W$, the bottom-right block is the matrix of $\bar e$ on $V/W$, and the block below the diagonal is zero because $W$ is invariant. The trace of a block triangular matrix is the sum of the traces of its diagonal blocks. The same argument gives $\det e = \det(e|_W)\det(\bar e)$ and the factorization of characteristic polynomials. A variant replaces the quotient by any surjection $q : V \to V'$ intertwining $e$ with an endomorphism of $V'$; it is used for traces in algebraic number theory.

## Statements

- [Trace is additive over an invariant subspace](trace-eq-trace-restrict-add-trace-map-q.md)
- [Trace splits along a surjective intertwining map](trace-eq-trace-restrict-ker-add-of-surje.md): the same splitting along a surjective intertwining map
