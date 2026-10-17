---
article_id: af_cfc61125046d27d4dffc5a21
declaration: def
origin: cited
statement: formalized
lean: TorGroup
---

# Definition 23.76

Let $A$ be a left $R$-module and let $M$ be a right $R$-module. $\operatorname{Tor}_{n}^{R}(M, A)$ is the abelian group $H_{n}(P_{*}^{A})$ uniquely determined by Theorem 23.75 using any projective resolution $P$ of $M$. If $\alpha: A \rightarrow B$ is a morphism of left $R$-modules the map $x \otimes a \mapsto x \otimes \varphi(a)$ induces a morphism $P_{*}^{A} \rightarrow P_{*}^{B}$ and morphisms $\operatorname{Tor}_{n}^{R}(M, \alpha): \operatorname{Tor}_{n}^{R}(M, A) \rightarrow \operatorname{Ext}_{n}^{R}(M, B)$ for each $n \geq 0$. This yields a family of functors $\operatorname{Tor}_{n}^{R}(M, \bullet)$ from the category of left $R$-modules to the category of abelian groups that is a homological $\delta$-functor.

## Depends on

- [Definition 23.9](../section-23/453-definition-23-9.md)
- [Definition 23.49](../section-23-7-subsection-23-7-1/489-definition-23-49.md)
- [Definition 23.56](../section-23-7-subsection-23-7-2/496-definition-23-56.md)
- [Theorem 23.75](510-theorem-23-75.md)

## Proof depends on

- [Theorem 23.50](../section-23-7-subsection-23-7-1/490-theorem-23-50.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.7.4](../../../../../../sources/v1/NumberTheoryI.md)
