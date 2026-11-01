---
article_id: af_2e62a94767d0aed67af344cf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Section19.subgroup_dual_correspondence
---

# Proposition 18.40

Let $G$ be a finite abelian group. There is an inclusion reversing bijection $\varphi$ between subgroups $H$ of $G$ and subgroups $K$ of $\widehat{G}$ defined by $\varphi(H) \coloneqq \{\chi \in \widehat{G} : \chi(h) = 1 \text{ for all } h \in H\}$. The inverse bijection $\phi$ is given by $\phi(K) \coloneqq \{g \in G : \chi(g) = 1 \text{ for all } \chi \in K\}$ and $\widehat{H} \simeq \widehat{G}/\varphi(H)$ and $\widehat{K} \simeq G/\phi(K)$; in particular, $\# H = [\widehat{G} : \varphi(H)]$ and $\# K = [G : \phi(K)]$.

## Depends on

- [Definition 18.31](376-definition-18-31.md)

## Proof depends on

- [Proposition 18.33](377-proposition-18-33.md)
- [Proposition 18.37](380-proposition-18-37.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.6](../../../../../../sources/v1/NumberTheoryI.md)
