# Integer matrices with the golden eigenvector

Let $\tau = (1 + \sqrt 5)/2$ be the golden
ratio and $\tau' = (1 - \sqrt 5)/2$ its conjugate, and let $M$ be a $2 \times 2$ integer matrix.
Then $(\tau, 1)^T$ is a right eigenvector of $M$, that is, $M (\tau, 1)^T = c\,(\tau, 1)^T$ for
some real number $c$, if and only if

$$M = \begin{pmatrix} m + n & m \\ m & n \end{pmatrix}$$

for some integers $m$ and $n$. In that case the characteristic polynomial of $M$ is
$(X - (n + m\tau))(X - (n + m\tau'))$, so the eigenvalues of $M$ are $n + m\tau$ and
$n + m\tau'$.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 39 (`jis-2025-25.1.5-lem-39`).
