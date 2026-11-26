# Homomorphism criterion for containment of conjunctive queries with inequalities

For a conjunctive query with inequalities $q(\bar x)$, write $q^+$ for its relational part, and let $H_q$ be the set of
maps $h$ from the variables and constants of $q$ to the variables and constants of $q$ that are the identity on
constants and satisfy $h(v) \ne h(v')$ for every inequality $v \ne v'$ of $q$. For $h \in H_q$, $h(q^+)$ is the
conjunctive query $\mathrm{Answer}(h(\bar x)) \mathrel{:-} R_1(h(\bar u_1)), \dots, R_n(h(\bar u_n))$. A homomorphism
from $q'(\bar x')$ to such a query $p(\bar y)$ is a map from the variables and constants of $q'$ to those of $p$ that is
the identity on constants, maps every relational atom of $q'$ to an atom of $p$, maps $\bar x'$ to $\bar y$, and maps
the two sides of every inequality of $q'$ to distinct terms.

For conjunctive queries with inequalities $q(\bar x)$ and $q'(\bar x')$, $q \subseteq q'$ if and only if, for every
$h \in H_q$, there is a homomorphism from $q'(\bar x')$ to $h(q^+)(h(\bar x))$. The plain homomorphism criterion of
the constant-free case fails here: $\mathrm{Answer} \mathrel{:-} \mathrm{Edge}(x, y)$ is not contained in
$\mathrm{Answer} \mathrel{:-} \mathrm{Edge}(x', y'), x' \ne y'$, although the second maps to the first.

## Depends on

- [Conjunctive queries with inequalities](conjunctive-queries-with-inequalities.md)

## Proof depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Informally uses

- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Example 30.7 (p. 268), the definition of $H_q$ and Theorem 30.8 (p. 269).
