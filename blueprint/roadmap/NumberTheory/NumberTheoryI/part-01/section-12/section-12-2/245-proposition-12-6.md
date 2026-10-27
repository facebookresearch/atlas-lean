---
article_id: af_9fdf2510a240096546e17583
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: discr_eq_det_embeddingsMatrix_sq
---

# Proposition 12.6

Let $L/K$ be a finite separable extension of degree $n$, and let $\Omega/K$ be a field extension for which there are distinct $\sigma_1, \ldots, \sigma_n \in \operatorname{Hom}_K(L, \Omega)$. For any $e_1, \ldots, e_n \in L$ we have $\operatorname{disc}(e_1, \ldots, e_n) = \det[\sigma_i(e_j)]_{ij}^2$, and for any $x \in L$ we have $\operatorname{disc}(1, x, x^2, \ldots, x^{n-1}) = \prod_{i\lt j}(\sigma_i(x) - \sigma_j(x))^2$. Such a field extension $\Omega/K$ always exists, since $L/K$ is separable ($\Omega = K^{\text{sep}}$ works).

## Depends on

- [Definition 4.3](../../section-4/section-4-1/part-01/058-definition-4-3.md)
- [Definition 4.17](../../section-4/section-4-1/part-01/072-definition-4-17.md)
- [Definition 12.5](244-definition-12-5.md)

## Proof depends on

- [Theorem 4.50](../../section-4/section-4-3/093-theorem-4-50.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 12.2](../../../../../../sources/v1/NumberTheoryI.md)
