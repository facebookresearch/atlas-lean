# Containment of unions of conjunctive queries

A union of conjunctive queries (UCQ) of arity $k$ is a finite union $q = q_1 \cup \dots \cup q_n$, $n \ge 1$, of
conjunctive queries $q_i = \mathrm{Answer}(\bar x) \mathrel{:-} \beta_i$, possibly with constants, that share one head tuple
$\bar x$ of length $k$ (after renaming the other variables apart), with $q(D) = q_1(D) \cup \dots \cup q_n(D)$; containment and
equivalence of UCQs are defined as for conjunctive queries.

**Theorem (Sagiv–Yannakakis).** For UCQs $q = q_1 \cup \dots \cup q_n$ and $q' = q'_1 \cup \dots \cup q'_m$ of the same
arity, $q \subseteq q'$ if and only if for every $i \in [n]$ there is $j \in [m]$ with $q_i \subseteq q'_j$. Combined with the
[homomorphism theorem](homomorphism-theorem-for-conjunctive-queries-with-constants.md), containment of UCQs reduces to
homomorphism tests between their disjuncts.

## Depends on

- [Containment, equivalence and homomorphisms of conjunctive queries](containment-equivalence-and-homomorphisms-of-conjunctive-queries.md)
- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)
- [Homomorphism theorem for conjunctive queries with constants](homomorphism-theorem-for-conjunctive-queries-with-constants.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 29.1 (p. 261).
- Y. Sagiv and M. Yannakakis, "Equivalences among relational expressions with the union and difference operators", *J. ACM* 27(4) (1980) 633–655, as credited by Abiteboul, Hull and Vianu, Exercise 6.14.
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Exercise 6.14.
