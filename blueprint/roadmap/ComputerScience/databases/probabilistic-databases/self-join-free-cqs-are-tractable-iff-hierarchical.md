# Self-join-free conjunctive queries: polynomial time when hierarchical, #P-hard otherwise

Let $q$ be a Boolean conjunctive query without self-joins (every atom uses a different relation name). If $q$ is
hierarchical, computing $p(q)$ on tuple-independent probabilistic databases $(A, p)$ takes polynomial time by the
following recurrence on the structure of $q$. Write $q$ as $f_0$, the atoms without variables, together with its
connected components $f_1(x_1), \dots, f_m(x_m)$, where each $x_i$ is a maximal variable of its component (no
variable $y$ has $\mathrm{sg}(x_i) \subsetneq \mathrm{sg}(y)$), so that $x_i$ occurs in every atom of $f_i$; then

$$p(q) = p(f_0) \cdot \prod_{i=1}^m \Big(1 - \prod_{a \in A} \big(1 - p(f_i[a/x_i])\big)\Big),$$

which is correct because $f_i[a/x_i]$ and $f_j[a'/x_j]$ are independent whenever $i \ne j$ or $a \ne a'$. If $q$ is
not hierarchical, the problem is $\#P$-hard; a query without self-joins is its own minimal equivalent query.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [Hierarchical conjunctive queries](hierarchical-conjunctive-queries.md)

## Proof depends on

- [Conjunctive queries whose minimal equivalent query is not hierarchical are #P-hard on probabilistic databases](non-hierarchical-conjunctive-queries-are-sharp-p-hard.md)
- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Theorem 1.3 and the recurrence (3) that follows it (p. 294), credited there to the authors' earlier paper in VLDB 2004.
