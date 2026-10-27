---
article_id: af_d8fb92296897d3ba02e84b6f
declaration: def
origin: cited
statement: formalized
lean: BSGSOrder.computeOrder
---

# Algorithm 7.4

Given an element $P$ of an additive group and the prime factorization
 $M=p_{1}^{e_{1}} \cdots p_{r}^{e_{r}}$ of an integer $M$ for which $MP=0$,
 compute the order of $P$ as follows: 1. Let $m=M=p_{1}^{e_{1}} \cdots
 p_{r}^{e_{r}}$. 2. For each prime $p_{i}$, while $p_{i} \mid m$ and
 $(m/p_{i})P=0$, replace $m$ by $m/p_{i}$. 3. Output $m$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 7.4](../../../../../sources/v1/EllipticCurves.md)
