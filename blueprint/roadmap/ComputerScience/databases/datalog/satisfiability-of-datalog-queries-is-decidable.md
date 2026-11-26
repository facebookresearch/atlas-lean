# Satisfiability of Datalog queries is decidable

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$. The query is satisfiable if $q(D) \ne \emptyset$ for some database $D$.

Let $a_1, \dots, a_n$ be the constants of $\Pi$ and $\star$ a further constant, and let $D_\Pi$ contain every fact over
the extensional relation names of $\Pi$ with arguments in $\{\star, a_1, \dots, a_n\}$. Then $q$ is satisfiable if and
only if $q(D_\Pi) \ne \emptyset$. Consequently satisfiability of Datalog queries is decidable in exponential time, and in
polynomial time for Datalog queries whose programs mention no constants.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [The class EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)
- [Datalog queries are monotone and homomorphism-preserved; CQ-in-Datalog containment](datalog-queries-are-monotone-and-homomorphism-preserved-cq-i.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), Theorem 38.1 and Lemma 38.2 (pp. 345–346).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Theorem 12.5.2 (p. 301).
