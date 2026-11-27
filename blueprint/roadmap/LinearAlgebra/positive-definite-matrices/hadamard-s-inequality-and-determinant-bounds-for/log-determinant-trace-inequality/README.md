# Log-determinant trace inequality

Let $A$ and $B$ be positive definite real square matrices indexed by a finite set with $n$ elements.
Then $\log(\det A \cdot \det B) \le \operatorname{tr}(AB) - n$.

## Idea

The matrix $B^{1/2} A B^{1/2}$ is positive definite, with determinant $\det A \det B$ and trace
$\operatorname{tr}(AB)$. Summing $\log \lambda \le \lambda - 1$ over its eigenvalues gives the
inequality, with equality exactly when every eigenvalue is $1$, that is when $AB = I$. It is the
nonnegativity of a Kullback–Leibler divergence between centred Gaussian laws:
$2\,\mathrm{KL}(\mathcal N(0, A) \,\|\, \mathcal N(0, B^{-1})) = \operatorname{tr}(AB) - n - \log \det(AB)$.

## Statements

- [Log-determinant trace inequality](log-det-mul-le-trace.md)
