---
article_id: af_39e543d3371cf1007cb85f91
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: RiemannZetaFunction.riemannZeta_eq_tsum_one_div_nat_cpow
---

# Definition 16.1

The Riemann zeta function is the complex function defined by the series $\zeta(s)\coloneqq \sum_{n \geq 1} n^{-s}$ for $\operatorname{Re}(s)>1$, where $n$ varies over positive integers. It is easy to verify that this series converges absolutely and locally uniformly on $\operatorname{Re}(s)>1$ (use the integral test on an open ball strictly to the right of the line $\operatorname{Re}(s)=1$). By Theorem 16.17, it defines a holomorphic function on $\operatorname{Re}(s)>1$, since each term $n^{-s}=e^{-s \log n}$ is holomorphic.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 16.1](../../../../../../sources/v1/NumberTheoryI.md)
