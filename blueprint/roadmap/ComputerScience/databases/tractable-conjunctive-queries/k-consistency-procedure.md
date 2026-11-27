# The k-consistency procedure for Boolean conjunctive queries

Let $q = \mathrm{Answer}() \mathrel{:-} R_1(\bar u_1), \dots, R_m(\bar u_m)$ be a Boolean conjunctive query, $D$ a
database and $k \ge 1$. For a nonempty $S \subseteq \{1, \dots, m\}$ let $q_S(\bar x_S)$ be the conjunctive query
with the atoms $R_i(\bar u_i)$, $i \in S$, whose output tuple lists the variables of these atoms. The $k$-consistency
procedure starts with $\mathrm{Cons}_S = q_S(D)$ for every $S$ with $1 \le |S| \le k$. While some $\mathrm{Cons}_S$
contains a tuple that agrees on the common variables with no tuple of some $\mathrm{Cons}_{S'}$, it replaces
$\mathrm{Cons}_S$ by the semijoin $\mathrm{Cons}_S \ltimes \mathrm{Cons}_{S'}$, the tuples of $\mathrm{Cons}_S$ that
agree with some tuple of $\mathrm{Cons}_{S'}$. When no such pair remains, it fails if some $\mathrm{Cons}_S$ is empty
and succeeds otherwise. It uses no decomposition of $q$. For $k = 1$ the sets $S$ are single atoms, and this is the
consistency procedure for acyclic queries. Each replacement removes a tuple, so for fixed $k$ the procedure runs in time
$O(\lVert D \rVert^{2k} \cdot \lVert q \rVert^{2k})$.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [One semijoin command](../join-processing/semijoin-step.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Algorithm 7 (p. 164), Algorithm 9 ($k$-Consistency) and the running-time analysis that follows it (pp. 186–187).
