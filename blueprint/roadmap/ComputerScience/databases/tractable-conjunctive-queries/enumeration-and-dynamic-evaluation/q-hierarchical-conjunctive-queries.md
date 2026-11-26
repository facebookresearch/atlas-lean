# Q-hierarchical conjunctive queries

For a conjunctive query $\varphi$ and a variable $x$, let $\mathrm{atoms}(x)$ be the set of atoms of $\varphi$ that contain $x$.
$\varphi$ is *q-hierarchical* if for any two variables $x, y$ of $\varphi$:

1. $\mathrm{atoms}(x) \subseteq \mathrm{atoms}(y)$, or $\mathrm{atoms}(x) \supseteq \mathrm{atoms}(y)$, or
   $\mathrm{atoms}(x) \cap \mathrm{atoms}(y) = \emptyset$; and
2. if $\mathrm{atoms}(x) \subsetneq \mathrm{atoms}(y)$ and $x$ is free, then $y$ is free.

A Boolean conjunctive query is q-hierarchical if and only if it is [hierarchical](../../probabilistic-databases/hierarchical-conjunctive-queries.md).
The queries $\exists x \exists y\, (Sx \wedge Exy \wedge Ty)$ and $\varphi(x) = \exists y\, (Exy \wedge Ty)$ are not q-hierarchical,
violating conditions 1 and 2 respectively. Whether a conjunctive query is q-hierarchical can be decided in polynomial time.

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Hierarchical conjunctive queries](../../probabilistic-databases/hierarchical-conjunctive-queries.md)

## Sources

- C. Berkholz, J. Keppeler and N. Schweikardt, "Answering conjunctive queries under updates", *Proceedings of the 36th ACM PODS*, 2017, pp. 303–318; arXiv:1702.06370 <https://arxiv.org/abs/1702.06370>, Definition 3.1, the examples (2)–(4) and Lemma 4.2.
