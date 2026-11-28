# Answers of a conjunctive query

Fix a countably infinite set of constants and a disjoint set of variables. A conjunctive query $q(\bar x)$ over a
relational schema is written $\mathrm{Answer}(\bar x) \mathrel{:-} R_1(\bar u_1), \dots, R_n(\bar u_n)$ with $n \ge 1$,
where each $\bar u_i$ is a tuple of constants and variables, every variable of the head tuple $\bar x$ occurs in some
$\bar u_i$, and the arity of $q$ is the length of $\bar x$; the variables of the body that are not in $\bar x$ are
existentially quantified, and $q$ is Boolean when $\bar x$ is empty. This extends the constant-free syntax of
[CQ](conjunctive-queries-and-the-chandra-merlin-theor/cq.md) by constants in atoms. An assignment for $q$ over a database
$D$ maps each variable of $q$ to an element of the active domain $\mathrm{Dom}(D)$ and is extended to constants as the
identity; it is consistent with $D$ when it maps every body atom to a fact of $D$. The answer set of $q$ on $D$ is

$$q(D) = \{\eta(\bar x) : \eta \text{ an assignment for } q \text{ over } D \text{ consistent with } D\} \subseteq \mathrm{Dom}(D)^k,$$

where $k$ is the arity of $q$; for Boolean $q$, $D \models q$ means that $q(D)$ contains the empty tuple. Equivalently,
$q(D)$ is the set of tuples $h(\bar x)$ over all maps $h$ from the variables and constants of $q$ to $\mathrm{Dom}(D)$
that are the identity on constants and send every body atom to a fact of $D$.

## Depends on

- [CQ](conjunctive-queries-and-the-chandra-merlin-theor/cq.md)
- [Satisfaction of a conjunctive-query body](conjunctive-queries-and-the-chandra-merlin-theor/satisfies.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 12.1 and the semantics following Example 12.2 (pp. 93–94), and Theorem 13.2 (p. 102).
