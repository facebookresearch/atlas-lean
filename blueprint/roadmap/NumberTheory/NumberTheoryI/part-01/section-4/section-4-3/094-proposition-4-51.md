---
article_id: af_e28eab4d3c7cb1e0a651f417
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: norm_eq_prod_roots_pow
---

# Proposition 4.51

Let $L/K$ be a (not necessarily separable) finite extension, let $\bar{K}$ be an algebraic closure of $K$ containing $L$. Let $\alpha \in L^{\times}$ have minimal polynomial $f \in K[x]$ with factorization $f(x) = \prod_{i=1}^{d}(x - \alpha_i)$ in $\bar{K}[x]$, and let $e = [L:K(\alpha)]$. We have $\mathrm{N}_{L/K}(\alpha) = \prod_{i=1}^{d} \alpha_i^e$ and $\mathrm{T}_{L/K}(\alpha) = e \sum_{i=1}^{d} \alpha_i$. In particular, if $f(x) = \sum_{i=0}^{d} a_i x^i$, then $\mathrm{N}_{L/K}(\alpha) = (-1)^{de} a_0^e$ and $\mathrm{T}_{L/K}(\alpha) = -e a_{d-1}$.

## Depends on

- [Definition 4.46](091-definition-4-46.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 4.3](../../../../../../sources/v1/NumberTheoryI.md)
