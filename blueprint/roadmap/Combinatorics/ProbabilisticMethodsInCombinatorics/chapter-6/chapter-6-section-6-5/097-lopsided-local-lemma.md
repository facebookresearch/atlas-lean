---
article_id: af_8c2ace22d52f29e6f0e9e39a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LopsidedLLL.lopsided_local_lemma
---

# Theorem 6.5.1 (Lopsided local lemma)

Let $A_1, \ldots, A_n$ be events. For each $i$, let $N(i) \subseteq [n]$ be such that $\mathbb{P}(A_i \mid \bigwedge_{j \in S} \overline{A_j}) \leq \mathbb{P}(A_i)$ for all $i \in [n]$ and $S \subseteq [n] \setminus (N(i) \cup \{i\})$. Suppose there exist $x_1, \ldots, x_n \in [0,1)$ such that $\mathbb{P}(A_i) \leq x_i \prod_{j \in N(i)} (1 - x_j)$ for all $i \in [n]$. Then $\mathbb{P}(\text{none of the events } A_i \text{ occur}) \geq \prod_{i=1}^n (1 - x_i)$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 6, Section 6.5](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
