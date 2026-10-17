---
article_id: af_4132aba02e10b25d6e2f8109
declaration: theorem
origin: cited
statement: formalized
lean: cauchy_residue_formula
---

# Theorem 16.25 (Cauchy Residue Formula)

Let $U$ be an open set containing a simple closed curve $\gamma$. Let $f$ be a function that is meromorphic on $U$, let $z_1, \ldots, z_n$ be the poles of $f$ that lie in the interior of $\gamma$, and suppose that no pole of $f$ lies on $\gamma$. Then $$\int_{\gamma} f(z)\, dz = 2\pi i \sum_{i=1}^n \operatorname{res}_{z_i}(f).$$

## Depends on

- [Definition 16.21](331-definition-16-21.md)
- [Definition 16.22](332-definition-16-22.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 16.3.3](../../../../../../sources/v1/NumberTheoryI.md)
