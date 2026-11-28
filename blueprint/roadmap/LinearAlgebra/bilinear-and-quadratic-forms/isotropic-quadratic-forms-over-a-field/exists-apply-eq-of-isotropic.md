# A nondegenerate quadratic form with a nonzero zero represents every element

Let $K$ be a
field in which $2$ is invertible (that is, of characteristic different from $2$), let $V$ be a
$K$-vector space and let $Q$ be a nondegenerate quadratic form on $V$. If $Q(v) = 0$ for some
nonzero $v \in V$, then $Q$ represents every element of $K$: for every $c \in K$ there is
$w \in V$ with $Q(w) = c$.

Nondegeneracy is `QuadraticMap.Nondegenerate`; as $2$ is invertible, it says that the symmetric
bilinear form $B$ with $Q(x) = B(x, x)$ is nondegenerate
(`QuadraticMap.nondegenerate_associated_iff`). The statement needs no finiteness of $V$.

## Sources

- A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, lecture notes, Lecture 9, Theorem 9.9 and its proof, p. 3.
