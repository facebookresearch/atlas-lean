# Conjunctive queries are preserved under homomorphisms

For a finite set $C$ of constants, write $(D, \bar a) \to_C (D', \bar b)$ for databases $D, D'$ and tuples
$\bar a, \bar b$ of equal length when there is a map $h$ from $\mathrm{Dom}(D)$ to $\mathrm{Dom}(D')$ that is the
identity on $C \cap \mathrm{Dom}(D)$, sends every fact $R(c_1, \dots, c_m)$ of $D$ to a fact $R(h(c_1), \dots, h(c_m))$
of $D'$, and satisfies $h(\bar a) = \bar b$.

Let $q(\bar x)$ be a $k$-ary conjunctive query and let $C$ be the set of constants occurring in $q$. For all
databases $D, D'$ and tuples $\bar a \in \mathrm{Dom}(D)^k$, $\bar b \in \mathrm{Dom}(D')^k$, if
$(D, \bar a) \to_C (D', \bar b)$ and $\bar a \in q(D)$, then $\bar b \in q(D')$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the definition of $\to_C$ before Example 13.4 (p. 103), Definition 13.5 and Proposition 13.6 (p. 104).
