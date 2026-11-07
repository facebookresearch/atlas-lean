# Triangularization of a matrix with split characteristic polynomial

Let $K$ be a field, let
$n$ be a finite linearly ordered index set, and let $A$ be a square matrix over $K$ with rows and
columns indexed by $n$ whose characteristic polynomial splits over $K$. Then there are an
invertible matrix $P$ and a matrix $T$, both over $K$ and indexed by $n$, such that $T$ is upper
triangular ($T_{ij} = 0$ whenever $j < i$) and $A = P T P^{-1}$.

Proof: triangularize the endomorphism of $K^n$ given by $A$ in the standard basis, and conjugate
by the change-of-basis matrix from the standard basis to the triangularizing basis.

## Sources

- Mathlib `docs/undergrad.yaml`, Linear algebra / Structure theory of endomorphisms / triangularization; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 2.3.1.
