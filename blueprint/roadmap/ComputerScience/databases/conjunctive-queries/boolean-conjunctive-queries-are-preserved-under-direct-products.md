# Boolean conjunctive queries are preserved under direct products

Fix a bijection $\tau$ from pairs of constants to constants. The direct product $D \otimes D'$ of two databases over a
schema $S$ contains, for each relation name $R$ of $S$ of arity $n$, exactly the facts
$R(\tau(a_1, a'_1), \dots, \tau(a_n, a'_n))$ with $R(a_1, \dots, a_n) \in D$ and $R(a'_1, \dots, a'_n) \in D'$.

Every Boolean conjunctive query $q$ without constants over $S$ is preserved under direct products: if $D \models q$
and $D' \models q$, then $D \otimes D' \models q$. Whether a Boolean first-order query without constants holds in
$D \otimes D'$ does not depend on the choice of $\tau$; a query mentioning a constant $a$ can tell whether
$\tau(a, a) = a$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the definition of direct products of databases (p. 105), Definition 13.8 and Proposition 13.9 (p. 106).
