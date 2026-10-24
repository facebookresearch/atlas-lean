---
article_id: af_91efff6b7bc8c97dc6f7b6d3
declaration: abbrev
origin: cited
statement: formalized
lean: IsCompleteSpace
---

# Definition 8.1

Let $X$ be a metric space. A sequence $(x_n)$ of elements of $X$ converges (to $x$) if there is an $x \in X$ such that for every $\epsilon > 0$ there is an $N \in \mathbb{Z}_{>0}$ such that $d(x_n, x) < \epsilon$ for all $n \geq N$; the limit $x$ is necessarily unique. The sequence $(x_n)$ is Cauchy if for every $\epsilon > 0$ there is an $N \in \mathbb{Z}_{>0}$ such that $d(x_m, x_n) < \epsilon$ for all $m, n \geq N$. Every convergent sequence is Cauchy, but the converse need not hold. A metric space in which every Cauchy sequence converges is said to be complete.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 8.1](../../../../../sources/v1/NumberTheoryI.md)
