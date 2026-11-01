---
article_id: af_19ee21e4972d824cd73a3774
declaration: theorem
origin: cited
lean: IntegerLongDivision.long_division_correct
---

# Algorithm 3.34 (Fast Euclidean division of polynomials)

Given $a, b \in \mathbb{F}_p[x]$ with $b$ monic, compute $q, r \in \mathbb{F}_p[x]$ such that $a = qb + r$ with $\deg r < \deg b$ as follows:
1. If $\deg a < \deg b$ then return $q = 0$ and $r = a$.
2. Let $m = \deg a - \deg b$ and $k = \lceil \lg m + 1 \rceil$.
3. Let $f = \operatorname{rev}(b)$ (reverse the coefficients of $b$).
4. Compute $g_0 = 1, g_i = (2g_{i-1} - fg_{i-1}^2) \bmod x^{2^i}$ for $i$ from 1 to $k$. (this yields $fg_k \equiv 1 \bmod x^{m+1}$).
5. Set $s = \operatorname{rev}(a) g_k \bmod x^{m+1}$ (now $\operatorname{rev}(b) s \equiv \operatorname{rev}(a) \bmod x^{m+1}$).
6. Return $q = x^{m - \deg s} \operatorname{rev}(s)$ and $r = a - bq$.

## Depends on

- [Definition 3.2](../section-3-1/006-definition-3-2.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.7](../../../../../../sources/v1/EllipticCurves.md)
