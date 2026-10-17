---
article_id: af_afebfb2a12cde13657d7096d
declaration: abbrev
origin: cited
statement: formalized
lean: IsPerfectSelfPairing
---

# Definition 5.6

Let $A$ be a commutative ring and $M$ an $A$-module. A (bilinear) pairing on $M$ is an $A$-linear map $\langle\cdot,\cdot\rangle: M \times M \rightarrow A$. Explicitly, this means that for all $u, v, w \in M$ and $\lambda \in A$ we have $\langle u+v, w\rangle = \langle u, w\rangle + \langle v, w\rangle$, $\langle u, v+w\rangle = \langle u, v\rangle + \langle u, w\rangle$, $\langle\lambda u, v\rangle = \langle u, \lambda v\rangle = \lambda\langle u, v\rangle$. If $\langle v,w\rangle = \langle w,v\rangle$ then $\langle\cdot,\cdot\rangle$ is symmetric, if $\langle v,w\rangle = -\langle w,v\rangle$ then $\langle\cdot,\cdot\rangle$ is skew-symmetric, and if $\langle v,v\rangle = 0$ then $\langle\cdot,\cdot\rangle$ is alternating. The pairing $\langle\cdot,\cdot\rangle$ induces an $A$-module homomorphism $\varphi: M \rightarrow M^{\vee}$ defined by $m \mapsto (n \mapsto \langle m, n\rangle)$. If $\ker \varphi = \{0\}$ then $\langle\cdot,\cdot\rangle$ is nondegenerate, and if $\varphi$ is an isomorphism then $\langle\cdot,\cdot\rangle$ is perfect.

## Depends on

- [Definition 5.1](097-definition-5-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 5.1](../../../../../../sources/v1/NumberTheoryI.md)
