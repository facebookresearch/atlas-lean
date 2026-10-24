---
article_id: af_fca37c58d51cf7de910cf9a4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CM6.strong_maximum_principle_full
---

# Theorem 5.1 (Strong Maximum Principle)

Let $\Omega \subset \mathbb{R}^{n}$ be a domain, and assume that $u \in C(\Omega)$ verifies the mean value property. Then if $u$ achieves its max or min at a point $p \in \Omega$, then $u$ is constant on $\Omega$. Therefore, if $\Omega$ is bounded and $u \in C(\bar{\Omega})$ is not constant, then for every $x \in \Omega$, we have $u(x)\lt \max_{y \in \partial \Omega} u(y)$ and $u(x)>\min_{y \in \partial \Omega} u(y)$.

## Depends on

- [Theorem 4.1 (Mean value properties)](029-mean-value-properties.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #6, Section 5 (Maximum Principle)](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
