# Datalog queries are preserved under homomorphisms

Let $q = (P, R)$ be a Datalog query of arity $k$ over a schema $\mathbf S$ and let $C$ be the set of constants of $P$. For
databases $D, D'$ over $\mathbf S$ and tuples $\bar a \in \mathrm{Dom}(D)^k$, $\bar b \in \mathrm{Dom}(D')^k$: if some map
$h : \mathrm{Dom}(D) \to \mathrm{Dom}(D')$ that is the identity on $C \cap \mathrm{Dom}(D)$ sends every fact of $D$ to a fact
of $D'$ and satisfies $h(\bar a) = \bar b$, and $\bar a \in q(D)$, then $\bar b \in q(D')$. For constant-free programs the
condition on $C$ is vacuous; for programs with constants it cannot be dropped.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Datalog queries are equivalent to infinitary unions of conjunctive queries](datalog-queries-are-equivalent-to-infinitary-ucqs.md)
- [Unions of conjunctive queries are preserved under homomorphisms](../../conjunctive-queries/cores-and-minimization/unions-of-conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 36.1 and Corollary 36.6 (pp. 329–334).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Lemma 12.5.1 (p. 301), for constant-free programs, and Exercise 12.21.
