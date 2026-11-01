---
article_id: af_e1d4edc2dc3cb545240a06f6
declaration: abbrev
origin: cited
statement: formalized
lean: GroupCohomology.nCochains
---

# Definition 23.3

Let $A$ be a $G$-module and let $n \in \mathbb{Z}_{\geq 0}$. The group of $n$-cochains is the abelian group $C^{n}(G, A)\coloneqq \operatorname{Map}(G^{n}, A)$ of maps of sets $f: G^{n} \rightarrow A$ under pointwise addition. We have $C^{0}(G, A) \simeq A$, since $G^{0}=\{1\}$ is a singleton set. The $n$th coboundary map $d^{n}: C^{n}(G, A) \rightarrow C^{n+1}(G, A)$ is the homomorphism of abelian groups defined by $d^{n}(f)(g_{0}, \ldots, g_{n})\coloneqq g_{0} f(g_{1}, \ldots, g_{n})-f(g_{0} g_{1}, g_{2}, \ldots, g_{n})+f(g_{0}, g_{1} g_{2}, \ldots, g_{n}) \cdots+(-1)^{n} f(g_{0}, \ldots, g_{n-2}, g_{n-1} g_{n})+(-1)^{n+1} f(g_{0}, \ldots, g_{n-1})$. The group $C^{n}(G, A)$ contains subgroups of $n$-cocycles and $n$-coboundaries defined by $Z^{n}(G, A)\coloneqq \ker d^{n}$ and $B^{n}(G, A)\coloneqq \operatorname{im} d^{n-1}$ with $B^{0}(G, A)\coloneqq \{0\}$.

## Depends on

- [Definition 23.1](446-definition-23-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.1](../../../../../../sources/v1/NumberTheoryI.md)
