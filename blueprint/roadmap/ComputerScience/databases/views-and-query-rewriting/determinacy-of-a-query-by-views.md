# Determinacy of a query by views

A set of views is said to determine a query when any two databases on which every view returns the same answer also give the same answer to the query. Finite determinacy quantifies over finite databases only; unrestricted determinacy over arbitrary, possibly infinite, structures.

Fix a relational schema. A database instance is a finite relational structure over it. Let $\mathcal{Q} = \{Q_1, \dots, Q_k\}$ be a finite set of queries (the views) and $Q_0$ a query, all over the same schema, and write $Q(\mathbb{D})$ for the answer of $Q$ on $\mathbb{D}$.

- $\mathcal{Q}$ *finitely determines* $Q_0$ if for all finite structures $\mathbb{D}_1, \mathbb{D}_2$,

$$
\bigl(\forall Q \in \mathcal{Q}:\ Q(\mathbb{D}_1) = Q(\mathbb{D}_2)\bigr) \Rightarrow Q_0(\mathbb{D}_1) = Q_0(\mathbb{D}_2).
$$

- $\mathcal{Q}$ *determines* $Q_0$ (unrestricted determinacy) if the same implication is required for all structures $\mathbb{D}_1, \mathbb{D}_2$, finite or infinite.

Unrestricted determinacy is the stronger notion, and strictly so for conjunctive queries (Gogacz and Marcinkowski give views $\mathcal{Q}$ and a query $Q_0$, all conjunctive, such that $\mathcal{Q}$ finitely determines $Q_0$ but does not determine it). In the terminology of Calvanese, De Giacomo, Lenzerini and Vardi, determinacy is losslessness under the exact view assumption.

The *conjunctive query finite determinacy problem* takes as input a finite set $\mathcal{Q}$ of conjunctive queries and a conjunctive query $Q_0$ and asks whether $\mathcal{Q}$ finitely determines $Q_0$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

Determinacy is the semantic condition behind answering a query from materialized views: if $\mathcal{Q}$ does not determine $Q_0$, no function of the view answers computes $Q_0$. A rewriting of $Q_0$ in terms of the views witnesses determinacy, but determinacy alone does not guarantee a rewriting in a given query language.

## Sources

- Tomasz Gogacz and Jerzy Marcinkowski, "Red Spider Meets a Rainworm: Conjunctive Query Finite Determinacy Is Undecidable", Proceedings of the 35th ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2016), pp. 121–134, 2016, <https://doi.org/10.1145/2902251.2902288>; definition of CQfDP in Section 1 of arXiv:1512.01681v1, <https://arxiv.org/abs/1512.01681v1>.
