# LWE with uniform errors has zero advantage

Let $R$ be a finite commutative ring and let the error vector $e$ be uniform on $R^m$. Then for every secret law, the real LWE pair $(A, A s + e)$ with $A$ uniform in $R^{m \times n}$ is distributed exactly as a uniform pair $(A, u)$, and is independent of $s$. Consequently every distinguisher has advantage $0$, so LWE hardness can only hold for error laws that are far from uniform.

## Proof sketch

For fixed $A$ and $s$, $e \mapsto A s + e$ is a bijection of $R^m$, so $A s + e$ is uniform and independent of $(A, s)$.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
