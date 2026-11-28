# Least-squares fixes of databases with numerical attributes

A least-squares fix of an inconsistent database changes only designated integer attributes, keeps keys and all other values, satisfies the integrity constraints, and minimizes the weighted sum of squared changes. Two decision problems are defined on top of it: whether a fix exists, and consistent query answering.

**Schema (Bertossi, Bravo, Franconi and Lopatenko).** A relational schema has a domain containing $\mathbb{Z}$, database predicates, built-in predicates and attributes. A database instance $D$ is a finite set of ground atoms $P(\bar c)$. A set $\mathcal{F}$ of *fixable* attributes takes values in $\mathbb{Z}$; the other attributes are *rigid*. Every relation $R$ has a primary key $K_R$ made of rigid attributes; the key constraints $\mathcal{K}$ hold in $D$ and in every fix. A separate set $IC$ of *flexible* integrity constraints may be violated by $D$.

**Constraints.** A *linear denial* is a sentence $\forall \bar x\, \neg(A_1 \wedge \cdots \wedge A_m)$ where each $A_i$ is a database atom, an atom $x \mathrel{\theta} c$ with a variable $x$, a constant $c$ and $\theta \in \{=, \ne, <, >, \le, \ge\}$, or an equality $x = y$; it is *extended* if atoms $x \ne y$ are also allowed. *Aggregation constraints* compare aggregates (sum, count, average) of attribute values with constants or with each other. They are *filtering* if a condition selects the tuples aggregated over, as in $\mathit{sum}(A_1 : A_2 = 3) > 5$; *multi-attribute* if the aggregated argument is an arithmetic combination of attributes, as in $\mathit{sum}(A_1 \times A_2) > 100$; and *single-relation* if all attributes come from one relation.

**Fixes.** For instances $D, D'$ with the same key values in every relation and weights $\alpha_A$ for $A \in \mathcal{F}$, the *square distance* is

$$
\Delta_{\bar\alpha}(D, D') = \sum_{R,\ A \in \mathcal{F},\ \bar k} \alpha_A \bigl(\pi_A(\bar t(\bar k, R, D)) - \pi_A(\bar t(\bar k, R, D'))\bigr)^2,
$$

where $\bar k$ ranges over the key values of $R$ and $\bar t(\bar k, R, D)$ is the tuple of $R$ in $D$ with key $\bar k$. A *fix* of $D$ with respect to $IC$ is an instance $D'$ with the same schema and domain, the same values as $D$ in every rigid attribute, satisfying $\mathcal{K}$ and $IC$. A *least-squares fix* (LS-fix) is a fix minimizing $\Delta_{\bar\alpha}(D, D')$ among all fixes; the source then takes all weights equal to $1$. If $D$ has a fix, it has an LS-fix (Proposition 1 of the source).

**Problems.** $\mathit{NE}$ is the set of pairs $(D, IC)$ such that $D$ has at least one LS-fix with respect to $IC$. For a conjunctive query $Q$ and a ground tuple $\bar t$, $\bar t$ is a *consistent answer* under the *skeptical* semantics if $D' \models Q(\bar t)$ for every LS-fix $D'$, under the *brave* semantics if for some LS-fix, and under the *majority* semantics if more LS-fixes satisfy $Q(\bar t)$ than do not. $\mathit{CQA}(Q, IC, \mathcal{S})$ is the problem of deciding, given $D$ and $\bar t$, whether $\bar t$ is a consistent answer under semantics $\mathcal{S}$.

Unlike the tuple-level repairs of Arenas, Bertossi and Chomicki, for which a consistent set of constraints always admits a repair, a fix may fail to exist even when the constraints are consistent: the source gives one relation $R(X, Y)$ with key $X$ and constraints forcing $2 \le Y \le 3$ with pairwise distinct $Y$ values, under which a three-tuple instance has no fix.

## Depends on

- [Relational schema](../dependencies-and-the-chase/relational-schema.md)
- [Database instance](../dependencies-and-the-chase/instance.md)
- [Grouping and aggregation semantics](grouping-and-aggregation-semantics.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

LS-fixes model the correction of erroneous measurements, such as census forms or traffic counts, by the smallest overall numerical change. With linear denials, the constraints cut out an intersection of half-spaces and LS-fixes lie on its border; an instance can have exponentially many LS-fixes.

## Sources

- Leopoldo Bertossi, Loreto Bravo, Enrico Franconi and Andrei Lopatenko, "Complexity and Approximation of Fixing Numerical Attributes in Databases Under Integrity Constraints", Database Programming Languages (DBPL 2005), Lecture Notes in Computer Science 3774, pp. 262–278, Springer, 2005, <https://doi.org/10.1007/11601524_17>. Read in arXiv:cs/0503032v3, <https://arxiv.org/abs/cs/0503032v3>; Section 2 (schema, linear denials, aggregation constraints), Definitions 1–4, Example 6 and Proposition 1, numbering of arXiv:cs/0503032v3.
- Leopoldo Bertossi, Loreto Bravo, Enrico Franconi and Andrei Lopatenko, "The complexity and approximation of fixing numerical attributes in databases under integrity constraints", Information Systems 33(4–5), pp. 407–434, 2008, <https://doi.org/10.1016/j.is.2008.01.005> (journal version, not read).
