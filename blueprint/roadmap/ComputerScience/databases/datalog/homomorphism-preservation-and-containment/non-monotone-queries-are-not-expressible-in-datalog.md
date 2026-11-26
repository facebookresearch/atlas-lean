# Non-monotone queries are not expressible in Datalog

If a query $Q$ over a schema $\mathbf S$ is not monotone, that is, $D \subseteq D'$ and $Q(D) \not\subseteq Q(D')$ for some
databases $D, D'$, then no Datalog query over $\mathbf S$ expresses $Q$, even when $Q$ is computable in polynomial time. For
example, the Boolean query asking whether an undirected graph is 2-colorable is not expressible in Datalog: adding edges
can destroy 2-colorability.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Datalog queries are monotone](datalog-queries-are-monotone.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Corollary 36.7 and Exercise 4.24.
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Exercises 12.10 and 12.12.
