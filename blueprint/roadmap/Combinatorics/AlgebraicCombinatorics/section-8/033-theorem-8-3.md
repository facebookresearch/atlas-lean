---
article_id: af_5deb40c7ea5133da28386dff
declaration: theorem
origin: cited
statement: formalized
lean: WalkTypeCount.walkTypeCount_eq_numSYT_mul_prod
---

# Theorem 8.3

Let $\lambda$ be a partition and $w=A_{n} A_{n-1} \cdots A_{1}$ a valid $\lambda$-word. Let $S_{w}=\{i \mid A_{i}=D\}$. For each $i \in S_{w}$, let $a_{i}$ be the number of $D$'s in $w$ to the right of $A_{i}$, and let $b_{i}$ be the number of $U$'s in $w$ to the right of $A_{i}$. Then $\alpha(w, \lambda)=f^{\lambda} \prod_{i \in S_{w}}(b_{i}-a_{i})$.

## Depends on

- [Lemma 8.1](031-lemma-8-1.md)

## Proof depends on

- [Lemma 8.2](032-lemma-8-2.md)

## Sources

- [MIT 18.318 Topics in Algebraic Combinatorics (Spring 2006), Section 8](../../../../sources/v1/AlgebraicCombinatorics.md)
