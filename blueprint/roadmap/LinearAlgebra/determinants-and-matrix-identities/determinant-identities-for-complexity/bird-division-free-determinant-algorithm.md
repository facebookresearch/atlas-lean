# Bird's division-free determinant algorithm

For an $n\times n$ matrix $A$ ($n \ge 1$) over a commutative ring define $X_1=A$ and $X_{t+1}=\mu(X_t)\,A$, where $\mu(X)$ is the matrix obtained from $X$ by zeroing the entries below the diagonal and replacing each diagonal entry $x_{ii}$ by $-\sum_{j>i}x_{jj}$. Then $\det A=(-1)^{n-1}(X_n)_{11}$. The algorithm computes $n - 1$ matrix products, hence uses $O(n^4)$ ring operations and no divisions, so it runs over any commutative ring.

## Proof sketch

The construction mirrors the Faddeev–LeVerrier/Samuelson–Berkowitz recursion for the characteristic polynomial: the diagonal replacement accumulates traces of partial products, and an induction on $t$ shows that the upper-left entry after $n$ rounds equals the signed determinant (Bird's proof via the action on characteristic coefficients).

## Depends on

- [Leibniz formula for the determinant](../determinants-of-matrices/leibniz-formula/det-apply.md)

## Proof depends on

- [Newton's trace identities for the characteristic polynomial](../../eigenvalues-and-canonical-forms/newton-s-identities-for-traces-of-matrix-powers/newton-s-identities/trace-cayley-hamilton-newton.md)

## Sources

- Richard S. Bird, "A Simple Division-Free Algorithm for Computing Determinants", Information Processing Letters 111(21-22), 2011.
