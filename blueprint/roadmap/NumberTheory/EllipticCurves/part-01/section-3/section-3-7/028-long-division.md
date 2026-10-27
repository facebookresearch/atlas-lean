---
article_id: af_c3bf45766c79bc3c3e88e786
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: IntegerLongDivision.long_division_correct
---

# Algorithm 3.37 (Long division)

Given positive integers $a = \sum_{i=0}^{m} a_i 2^i$ and $b = \sum_{i=0}^{n} b_i 2^i$, compute $q, r \in \mathbb{Z}$ such that $a = qb + r$ with $0 \leq r < b$ as follows:
1. If $b > a$ return $q = 0$ and $r = b$, and if $b = 1$ return $q = a$ and $r = 0$.
2. Set $q \leftarrow 0, r \leftarrow 0$, and $k \leftarrow m$.
3. While $k \geq 0$ and $r < b$ set $q \leftarrow 2q, r \leftarrow 2r + a_k$, and $k \leftarrow k - 1$.
4. If $r < b$ then return $q$ and $r$.
5. Set $q \leftarrow q + 1, r \leftarrow r - b$, and return to Step 3.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.7](../../../../../../sources/v1/EllipticCurves.md)
