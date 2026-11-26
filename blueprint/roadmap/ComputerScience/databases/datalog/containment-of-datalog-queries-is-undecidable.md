# Containment of Datalog queries is undecidable

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ whose rule heads contain only variables, each
occurring in the rule body (the cited source's Definition 35.1), and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

The problem that asks, for Datalog queries $q_1 = (\Pi_1, R_1)$ and $q_2 = (\Pi_2, R_2)$ over the same extensional
relation names and with output relations $R_1$, $R_2$ of the same arity, whether $q_1(D) \subseteq q_2(D)$ for every database $D$, is undecidable. The proof reduces
containment of context-free languages: a grammar in a suitable normal form is turned into a Datalog program whose
derivations over a database of labelled edges follow the parse trees of the grammar.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Inclusion of context-free languages is undecidable](../../../TheoryOfComputation/undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-language-le.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.1 (p. 319), Definition 35.16 and Proposition 35.17 (p. 327), Theorem 38.3 (p. 346) and Proposition 38.8 (p. 350).
- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Proposition 12.5.4 and Theorem 12.5.5 (p. 303).
