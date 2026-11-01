---
article_id: af_5b39a31b7af563dd047d30a7
declaration: def
origin: cited
---

# Definition 1.10

A valuation on a field $k$ is a group homomorphism $k^{\times} \rightarrow \mathbb{R}$ such that for all $x, y \in k$ we have $v(x+y) \geq \min(v(x), v(y))$. We may extend $v$ to a map $k \rightarrow \mathbb{R} \cup \{\infty\}$ by defining $v(0) \coloneqq \infty$. For any $0 < c < 1$, defining $|x|_v \coloneqq c^{v(x)}$ yields a nonarchimedean absolute value. The image of $v$ in $\mathbb{R}$ is the value group of $v$. We say that $v$ is a discrete valuation if its value group is equal to $\mathbb{Z}$. Given a field $k$ with valuation $v$, the set $A \coloneqq \{x \in k : v(x) \geq 0\}$ is the valuation ring of $k$ (with respect to $v$). A discrete valuation ring (DVR) is an integral domain that is the valuation ring of its fraction field with respect to a discrete valuation.

## Depends on

- [Definition 1.2](../section-1-2/001-definition-1-2.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 1.4](../../../../../../sources/v1/NumberTheoryI.md)
