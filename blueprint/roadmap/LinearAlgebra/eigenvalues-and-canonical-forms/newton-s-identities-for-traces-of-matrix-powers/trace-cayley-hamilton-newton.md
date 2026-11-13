# Newton's trace identities for the characteristic polynomial

Let $A$ be a square matrix
over a commutative ring $R$ whose rows and columns are indexed by a finite set of size $N$. For
each natural number $k$, let $c_k$ be the coefficient of $X^{N-k}$ in the characteristic
polynomial $\chi_A(X) = \det(X I - A)$ when $k \le N$, and $c_k = 0$ when $k > N$, so that
$\chi_A(X) = X^N + c_1 X^{N-1} + \dots + c_N$. Then for every natural number $k \ge 1$,

$$k \, c_k + \sum_{j=1}^{k} \operatorname{tr}(A^j) \, c_{k-j} = 0,$$

where $k$ is read as an element of $R$.

## Sources

- Knill, *Some fundamental theorems in mathematics*, §220. Problem `trace_cayley_hamilton_newton` of the lean-eval benchmark.
