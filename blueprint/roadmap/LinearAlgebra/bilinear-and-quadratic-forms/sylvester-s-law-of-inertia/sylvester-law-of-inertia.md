# Sylvester's law of inertia

Let $A$ and $B$ be real symmetric square matrices with rows
and columns indexed by a finite set $n$, and suppose $B = P^{\mathsf T} A P$ for some invertible
real matrix $P$ indexed by $n$. Then $A$ and $B$ have the same number of positive eigenvalues, the
same number of negative eigenvalues and the same number of zero eigenvalues, each counted with
multiplicity.

Proof: By the spectral theorem, the quadratic form of each matrix is a weighted sum of squares
whose weights are its eigenvalues. Congruence gives an equivalence of quadratic forms, and
invariance of the signature fixes the positive and negative counts; the zero count follows by
trichotomy.

## Sources

- J. J. Sylvester, *A demonstration of the theorem that every homogeneous quadratic polynomial is reducible by real orthogonal substitutions to the form of a sum of positive and negative squares*, Philosophical Magazine Ser. 4, 4(23) (1852), 138-142.
