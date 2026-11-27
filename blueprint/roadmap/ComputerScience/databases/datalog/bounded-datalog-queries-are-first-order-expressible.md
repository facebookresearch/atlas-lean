# Bounded Datalog queries are exactly those expressible in first-order logic

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$. For a Datalog program $\Pi$, a database $D$ and an intensional relation name $R$, the stage of $R$ is the least
$k$ such that $R$ has the same content after $k$ applications of the immediate-consequence operator to $D$ as in
$\Pi(D)$; the stage of $\Pi$ on $D$ is the least $k$ at which the whole iteration stabilizes. The query $(\Pi, R)$ is
bounded if the stage of $R$ is at most a fixed $k$ on every database, and the program $\Pi$ is bounded if its stage is
at most a fixed $k$ on every database.

For a Datalog query $q = (\Pi, R)$ over a schema $S$ the following are equivalent: (1) $q$ is bounded; (2) $q$ is
equivalent to a first-order query over $S$; (3) $q$ is equivalent to a union of conjunctive queries over $S$ with a common output tuple, in which a disjunct may also
contain equality atoms $y = z$ between two variables and $y = a$ between a variable and a constant, variables of the
output tuple included, each variable of the output tuple being equal, through these atoms, to a constant or to a
variable of a relational atom of the disjunct, or to the empty union of the arity of $R$, which denotes the empty
relation of that arity. The empty union is needed: over the empty extensional schema the rule $Q() \mathrel{:-} Q()$
defines a bounded query that is always false, and no conjunctive query over that schema has a relational atom.
Both kinds of equality are needed even for head-safe programs. The
rules $Q(x, x) \mathrel{:-} R(x)$ and $Q(x, y) \mathrel{:-} S(x, y)$ return the diagonal of $R$ together with $S$,
which is $(R(x) \wedge x = y) \vee S(x, y)$ with output $(x, y)$, and no common-output union without variable equalities
expresses it. And over a unary relation $R$, the rules $T(x, x) \mathrel{:-} R(x)$ and $Q(x) \mathrel{:-} T(x, c)$
define the bounded query that returns $\{c\}$ if $R(c)$ holds and nothing otherwise, which is
$R(x) \wedge x = c$; no union of conjunctive queries without constant equalities expresses it, since on $R = \{c, d\}$ a
disjunct that returns $c$ also returns $d$. A query
can be bounded while its program is not: with rules $P(x, y) \mathrel{:-} S(x, y)$, $P(x, y) \mathrel{:-} P(x, z), S(z, y)$,
$R(x, y) \mathrel{:-} S(x, y)$ and $R(x, y) \mathrel{:-} T(x, y)$, the query $(\Pi, R)$ is equivalent to
$S(x, y) \vee T(x, y)$.

## Expansion

This node states a precise result. The cited proof of (1) implies (2) unfolds the program into such a union, and (2) implies (3) uses
that a first-order query preserved under homomorphisms on finite databases is equivalent to a union of conjunctive
queries with such equalities
(the source's Theorem 28.11, a theorem of finite model theory). A good expansion links that theorem once a page for it
exists in Logic or Theory of Computation, and adds a page for the unfolding of a Datalog query into an infinitary union
of conjunctive queries (the source's Proposition 36.2) used for (1) implies (2). The union ranges over the unfoldings that use only input relations (the source's p. 332);
when there is none, as for $Q() \mathrel{:-} Q()$, it is empty and $q$ returns the empty relation on every database.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)

## Proof depends on

- [Datalog queries are equivalent to infinitary unions of conjunctive queries](homomorphism-preservation-and-containment/datalog-queries-are-equivalent-to-infinitary-ucqs.md)
- [Datalog queries are preserved under homomorphisms](homomorphism-preservation-and-containment/datalog-queries-are-preserved-under-homomorphisms.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), Definition 38.11 and Example 38.12 (p. 352), Definition 38.13 and Theorem 38.14 (p. 353).
