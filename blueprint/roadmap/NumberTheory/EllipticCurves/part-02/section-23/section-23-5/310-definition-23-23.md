---
article_id: af_b3f514099d4087b7dc999965
declaration: def
origin: cited
statement: formalized
lean: WeilPairing.millerFunction
---

# Definition 23.23

Let $E/k$ be an elliptic curve and let $P \in E(k)$. For each integer $n$ we
 recursively define the function $f_{n,P}$ via $$f_{0,P} = f_{1,P} \coloneqq
 1, \quad f_{n+1,P} \coloneqq f_{n,P} G_{P,nP}, \quad f_{-n,P} \coloneqq
 (f_{n,P} G_{nP,-nP})^{-1}$$ where $G_{P,Q}$ is as in Definition 23.16.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Definition 23.16](../section-23-3/303-definition-23-16.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 23.5](../../../../../../sources/v1/EllipticCurves.md)
