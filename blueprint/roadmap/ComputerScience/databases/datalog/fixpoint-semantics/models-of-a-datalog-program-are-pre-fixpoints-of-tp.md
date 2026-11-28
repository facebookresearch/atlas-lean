# Models of a Datalog program are the pre-fixpoints of its immediate consequence operator

Let $P$ be a Datalog program and $T_P$ its immediate consequence operator, as on
[the monotonicity page](the-immediate-consequence-operator-is-monotone.md). An instance $K$ over the schema of $P$ is a
model of $P$ (it satisfies every rule, read as a universally quantified implication) if and only if $T_P(K) \subseteq K$.
In particular every fixpoint of $T_P$ is a model of $P$; the converse fails in general.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [The immediate consequence operator is monotone](the-immediate-consequence-operator-is-monotone.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Lemma 12.3.1(ii) and (iii) (p. 283).
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Lemma 35.10(2) and (3) (pp. 324–325).
