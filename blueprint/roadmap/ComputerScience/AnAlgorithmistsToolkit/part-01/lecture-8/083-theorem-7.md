---
article_id: af_c616484f92845ed17db86310
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: PageRank.pageRank_termination
---

# Theorem 7 (Lecture 8, Section 3.3)

Fix $\epsilon > 0$. Suppose that in each iteration we pick a vertex $u$ with the property that $r(u) \geq \epsilon\, d(u)$. Then the process terminates in $O\!\left(\frac{1}{\epsilon \alpha}\right)$ iterations with vectors $p$ and $r$ that satisfy the following properties: 1. $\max_{v} \frac{r(v)}{d(v)} \leq \epsilon$. 2. $\operatorname{vol}(\operatorname{supp}(p)) \leq \frac{1}{\epsilon \alpha}$, where $\operatorname{supp}(p)$ is the set of vertices for which $p$ is nonzero and $\operatorname{vol}(S) \equiv \sum_{x \in S} d_x$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Proposition 6 (Lecture 8, Section 3.3)](082-proposition-6.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 8, Section 3.3](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
