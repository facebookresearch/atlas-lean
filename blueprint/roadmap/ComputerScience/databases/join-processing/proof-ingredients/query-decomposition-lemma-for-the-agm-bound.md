# Query decomposition lemma for the AGM bound

Let $q = R_1 \bowtie \dots \bowtie R_n$ be a join query over attribute set $X$ with schema $S$, let $f$ be a
[fractional edge cover](../natural-join-queries-their-hypergraphs-and-fractional-edge-c.md) of its hypergraph, and let $D$ be a
database in which every relation $R_i^D$ is nonempty. For $Y \subseteq X$ let $\mathcal R(Y)$ be the set of relations that
mention an attribute of $Y$, and let $q_Y$ be the join of the projections $\pi_{Y \cap S(R_i)}(R_i)$ over $R_i \in \mathcal R(Y)$.
For a tuple $\bar a$ write $R_i^D \ltimes \{\bar a\}$ for the set of tuples of $R_i^D$ that agree with $\bar a$ on their shared
attributes. Then for every partition $\{Y, Z\}$ of $X$,

$$\sum_{\bar a \in q_Y(D)} \ \prod_{R_i \in \mathcal R(Z)} \bigl|R_i^D \ltimes \{\bar a\}\bigr|^{f(S(R_i))} \le \prod_{i=1}^n \bigl|R_i^D\bigr|^{f(S(R_i))}.$$

The proof moves one attribute at a time from $Y$ to $Z$ and applies Hölder's inequality; with $Y = X$ it gives the
[AGM bound](../agm-output-size-bound-for-join-queries.md).

## Depends on

- [Natural join queries, their hypergraphs and fractional edge covers](../natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, definition (25.1) of $q_Y$, Theorem 25.10 (Hölder's inequality, stated) and Lemma 25.11 with its proof (pp. 212–215).
