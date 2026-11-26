# Hierarchical conjunctive queries

For a conjunctive query $q$ and a variable $x$ of $q$, let $\mathrm{sg}(x)$ be the set of atoms (subgoals) of $q$ that
contain $x$. The query $q$ is hierarchical if for any two variables $x, y$, either
$\mathrm{sg}(x) \cap \mathrm{sg}(y) = \emptyset$, or $\mathrm{sg}(x) \subseteq \mathrm{sg}(y)$, or
$\mathrm{sg}(y) \subseteq \mathrm{sg}(x)$. A Boolean conjunctive property is hierarchical if some hierarchical
conjunctive query defines it, equivalently if its minimal defining conjunctive query is hierarchical. For example,
$R(x), S(x, y)$ is hierarchical and $R(x), S(x, y), T(y)$ is not, since $\mathrm{sg}(x) = \{R, S\}$ and
$\mathrm{sg}(y) = \{S, T\}$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, the paragraph on hierarchical queries and Definition 1.2 (pp. 293–294).
