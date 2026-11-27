# Datalog queries are equivalent to infinitary unions of conjunctive queries

An infinitary union of conjunctive queries over a schema $\mathbf S$ is a disjunction
$\bigvee_{i \in N} \varphi_i(\bar x)$ over a possibly empty or infinite index set $N$ of conjunctive queries over $\mathbf S$ with the same free variables $\bar x$, in which a disjunct may also
contain equality atoms $y = z$ between two variables and $y = a$ between a variable and a constant, free variables
included, evaluated on
a database $D$ as the union of the answer sets $\varphi_i(D)$; the empty disjunction denotes the empty relation.

**Proposition.** For every Datalog query $q = (P, R)$ over a schema $\mathbf S$ whose rule heads contain only variables,
each occurring in the rule body (Definition 35.1 of the first source), there is an infinitary union of conjunctive
queries $q' = \varphi(\bar x)$ over $\mathbf S$ whose constants are those of $P$ and with $q \equiv q'$. The disjuncts can be
taken to be the conjunctive queries over $\mathbf S$ obtained from the rules for $R$ by repeatedly unfolding intensional
atoms with rules of $P$, that is, the expansion trees of $P$; when there is none, as for $Q() \mathrel{:-} Q()$, the union is empty. Both kinds of equality atom are needed: for the head-safe
rules $T(x, x) \mathrel{:-} E(x)$ and $Q(x) \mathrel{:-} T(x, c)$ the unfolding of $Q$ is $E(x) \wedge x = c$, and for
$Q(x, x) \mathrel{:-} E(x)$ and $Q(x, y) \mathrel{:-} S(x, y)$ it is $(E(x) \wedge x = y) \vee S(x, y)$.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

- [A Datalog program has a minimum model containing its input](../fixpoint-semantics/a-datalog-program-has-a-minimum-model-containing-its-input.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Proposition 36.2, Definition 36.3 and Lemmas 36.4 and 36.5 (pp. 330–334); the proof there is written out for Boolean queries.
- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Proposition 2.6 (expansion trees, p. 7 of the author copy).
