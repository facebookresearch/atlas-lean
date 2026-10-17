---
article_id: af_5f04cb2ce5fa4ddd2844f859
declaration: theorem
origin: cited
lean: Polynomial.yunAlgorithm_exists_sqfreeFactorization
---

# Algorithm 3.46

Given a monic polynomial $f \in \mathbb{F}_{q}[x]$ with $\operatorname{deg} f < \operatorname{char}(\mathbb{F}_{q})$, compute squarefree coprime polynomials $g_{1}, \ldots, g_{m} \in \mathbb{F}_{q}[x]$ with $g_{m} \neq 1$ such that $f=g_{1} g_{2}^{2} \cdots g_{m}^{m}$.
1. Compute $u=\operatorname{gcd}\left(f, f^{\prime}\right), v_{1}=f/u, w_{1}=f^{\prime}/u$, and set $i=1$.
2. Compute $g_{1}=\operatorname{gcd}\left(v_{1}, w_{1}-v_{1}^{\prime}\right)$.
3. While $v_{i} \neq g_{i}$:
   a. Compute $v_{i+1}$ with $v_{i}/g_{i}$ and $w_{i+1}=\left(w_{i}-v_{i}^{\prime}\right)/g_{i}$.
   b. Increment $i$ and compute $g_{i}=\operatorname{gcd}\left(v_{i}, w_{i}-v_{i}^{\prime}\right)$.
4. Set $m=i$ and return $g_{1}, \ldots, g_{m}$.

## Depends on

- [Definition 3.4](../section-3-1/007-definition-3-4.md)

## Proof depends on

- [Theorem 3.22](../section-3/020-theorem-3-22.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 3.11.2](../../../../../../sources/v1/EllipticCurves.md)
