---
article_id: af_7d6203de612d8c189ccc820a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FiniteFieldArith.fq_mul_complexity
---

# Theorem 3.35

Let $q = p^e$ be a prime power, and assume that $\log e = O(\log p)$. The
 time to multiply two elements of $\mathbb{F}_q$ is $O(\operatorname{M}(n)) =
 O(n \log n)$, where $n = \lg q$.

## Depends on

- [Definition 3.4](../section-3-1/007-definition-3-4.md)

## Proof depends on

- [Algorithm 3.34 (Fast Euclidean division of polynomials)](026-fast-euclidean-division-of-polynomials.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.7](../../../../../../sources/v1/EllipticCurves.md)
