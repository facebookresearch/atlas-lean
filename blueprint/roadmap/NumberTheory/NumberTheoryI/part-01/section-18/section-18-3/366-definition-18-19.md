---
article_id: af_de1bf474613aaba4115d5a83
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: DirichletLFunction.dirichletLFunction_eq_LSeries
---

# Definition 18.19

The Dirichlet $L$-function associated to a Dirichlet character $\chi$ is $$L(s, \chi)\coloneqq \prod_{p}\left(1-\chi(p) p^{-s}\right)^{-1}=\sum_{n \geq 1} \chi(n) n^{-s}.$$ The sum and product converge absolutely for $\operatorname{Re} s>1$, since $|\chi(n)| \leq 1$, thus $L(s, \chi)$ is holomorphic on $\operatorname{Re}(s)>1$.

## Depends on

- [Definition 18.5](../section-18-2/355-definition-18-5.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.3](../../../../../../sources/v1/NumberTheoryI.md)
