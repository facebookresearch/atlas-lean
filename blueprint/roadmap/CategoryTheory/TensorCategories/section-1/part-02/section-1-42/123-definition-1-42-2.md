---
article_id: af_ce66019055bfebfaf55ea928
declaration: structure
origin: cited
lean: BasedRingDef
---

# Definition 1.42.2

(1) A $\mathbb{Z}_{+}$-ring $A$ with basis $\{b_{i}\}_{i \in I}$ is called a based ring if the following conditions hold: [a] There exists a subset $I_{0} \subset I$ such that $1=\sum_{i \in I_{0}} b_{i}$. [b] Let $\tau: A \rightarrow \mathbb{Z}$ be the group homomorphism defined by $\tau(b_{i})=1$ if $i \in I_{0}$ and $\tau(b_{i})=0$ if $i \notin I_{0}$. There exists an involution $i \mapsto i^{*}$ of $I$ such that the induced map $a=\sum_{i \in I} a_{i} b_{i} \mapsto a^{*}=\sum_{i \in I} a_{i} b_{i^{*}}$ is an anti-involution of ring $A$ and such that $\tau(b_{i} b_{j})=1$ if $i=j^{*}$ and $\tau(b_{i} b_{j})=0$ if $i \neq j^{*}$. (2) A unital $\mathbb{Z}_{+}$-ring is a $\mathbb{Z}_{+}$-ring $A$ such that 1 belongs to the basis. (3) A multifusion ring is a based ring of finite rank. A fusion ring is a unital based ring of finite rank.

## Depends on

- [Definition 1.42.1](122-definition-1-42-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.42](../../../../../../sources/v1/TensorCategories.md)
