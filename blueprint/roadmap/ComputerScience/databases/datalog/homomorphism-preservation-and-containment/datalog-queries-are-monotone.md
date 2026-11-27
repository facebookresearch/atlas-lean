# Datalog queries are monotone

Every Datalog query $q = (P, R)$ over a schema $\mathbf S$ is monotone: for all databases $D \subseteq D'$ over $\mathbf S$,
$q(D) \subseteq q(D')$.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Datalog queries are preserved under homomorphisms](datalog-queries-are-preserved-under-homomorphisms.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Corollary 36.7 (p. 334).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Exercise 12.10.
