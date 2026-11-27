# Newton's identities for traces of matrix powers

Let $A$ be a square matrix over a commutative ring $R$, indexed by a finite set of size $N$, and write its characteristic polynomial as $\det(XI - A) = X^N + c_1 X^{N-1} + \dots + c_N$, with $c_0 = 1$ and $c_k = 0$ for $k > N$. Then for every $k \ge 1$,

$$k\,c_k + \sum_{j=1}^{k} \operatorname{tr}(A^j)\, c_{k-j} = 0,$$

where $k$ is read as an element of $R$.

## Idea

Over the complex numbers, the traces $\operatorname{tr}(A^j)$ are the power sums $\sum_i \lambda_i^j$ of the eigenvalues, and the coefficients $c_k$ are, up to sign, their elementary symmetric functions. Newton's identities, classically stated for the roots of a polynomial, relate the two families, so they let one compute the characteristic polynomial from the traces of the first $N$ powers, and conversely. For a $2 \times 2$ matrix they give $c_1 = -\operatorname{tr} A$ and $2c_2 = (\operatorname{tr} A)^2 - \operatorname{tr}(A^2)$, so $c_2 = \det A$. The identities hold over any commutative ring, but recovering $c_k$ requires dividing by $k$.

## Statements

- [Newton's trace identities for the characteristic polynomial](trace-cayley-hamilton-newton.md)
- [Characteristic-polynomial coefficients in descending order](charpoly-descending-coeff.md): the coefficients $c_k$ the identities relate to the traces
- [Traces of powers of a $2 \times 2$ matrix](trace-pow-two.md): a closed formula for the traces of powers of a $2 \times 2$ matrix, the case $N = 2$ worked out
