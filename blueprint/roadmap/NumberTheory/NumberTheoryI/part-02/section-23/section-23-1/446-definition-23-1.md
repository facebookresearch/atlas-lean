---
article_id: af_65ee0a651c7a6de4b47515dc
declaration: abbrev
origin: cited
statement: formalized
lean: GroupCohomology.GModule
---

# Definition 23.1

Let $G$ be a group. A $G$-module is an abelian group $A$ equipped with a $G$-action compatible with its group structure: $g(a+b)=ga+gb$ for all $g \in G$, $a, b \in A$. This implies $|ga|=|a|$ (where $|a|\coloneqq \#\langle a\rangle$ is the order of $a$); in particular $ga=0 \Leftrightarrow a=0$. A trivial $G$-module is an abelian group with trivial $G$-action: $ga=a$ for all $g \in G$, $a \in A$ (so every abelian group can be viewed as a trivial $G$-module). A morphism of $G$-modules is a morphism of abelian groups $\alpha: A \rightarrow B$ satisfying $\alpha(ga)=g\alpha(a)$. Kernels, images, quotients, and direct sums of $G$-modules are also $G$-modules.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.1](../../../../../../sources/v1/NumberTheoryI.md)
