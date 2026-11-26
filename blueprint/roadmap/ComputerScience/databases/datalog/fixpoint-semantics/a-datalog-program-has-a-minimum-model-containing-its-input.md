# A Datalog program has a minimum model containing its input

Let $P$ be a Datalog program and $I$ a finite instance over its extensional relations. Let $B(P, I)$ be the instance that
agrees with $I$ on the extensional relations and contains every intensional fact over $\mathrm{adom}(P, I)$, the
constants of $P$ and $I$. Then $B(P, I)$ is a model of $P$ containing $I$, and if $X$ is the set of all models of $P$ that
contain $I$, then

1. $\bigcap X$ is the minimum model of $P$ containing $I$, written $P(I)$;
2. $\mathrm{adom}(P(I)) \subseteq \mathrm{adom}(P, I)$; and
3. $P(I)$ agrees with $I$ on every extensional relation.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Definition 12.2.1, Lemma 12.2.2 and Theorem 12.2.3 (pp. 279–281).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 35.5, Proposition 35.6 and Theorem 35.8 (pp. 322–324).
