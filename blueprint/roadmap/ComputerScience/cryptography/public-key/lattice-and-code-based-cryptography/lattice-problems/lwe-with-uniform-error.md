# LWE with uniform errors has zero advantage

Let $R$ be a finite commutative ring and let the error vector $e$ be uniform on $R^m$. Then for every law of the secret $s$, with $A$ uniform in $R^{m \times n}$ and $A$, $s$, $e$ independent, the real LWE pair $(A, A s + e)$ is distributed exactly as a uniform pair $(A, u)$, and is independent of $s$. Consequently every distinguisher has advantage $0$: decision LWE with uniform error is hard for the trivial reason that the two distributions coincide, while the samples carry no information about $s$, so no algorithm recovers $s$ with higher probability than by guessing it from its law alone.

## Proof sketch

For fixed $A$ and $s$, $e \mapsto A s + e$ is a bijection of $R^m$, so $A s + e$ is uniform and independent of $(A, s)$.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
