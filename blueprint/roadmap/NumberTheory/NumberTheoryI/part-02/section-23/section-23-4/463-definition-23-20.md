---
article_id: af_3c4b5e0315e545da713d6c5a
declaration: abbrev
origin: cited
statement: formalized
lean: GroupCohomology.HomologyGroup
---

# Definition 23.20

Let $A$ be a $G$-module. The $n$th homology group of $G$ with coefficients in $A$ is the abelian group $H_{n}(G, A)\coloneqq \operatorname{Tor}_{n}^{\mathbb{Z}[G]}(\mathbb{Z}, A)$. If $\alpha: A \rightarrow B$ is a morphism of $G$-modules, the natural morphism $\alpha_{n}: H_{n}(G, A) \rightarrow H_{n}(G, B)$ is given by $x \otimes a \mapsto x \otimes \alpha(a)$. Each $H_{n}(G, \bullet)$ is a functor from the category of $G$-modules to the category of abelian groups.

## Depends on

- [Definition 23.1](../section-23-1/446-definition-23-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.4](../../../../../../sources/v1/NumberTheoryI.md)
