# Semipositive Datalog programs have a least model

Let $P$ be a semipositive $\mathrm{datalog}^\neg$ program, as defined on [the stratification page](stratifications-and-the-precedence-graph.md),
with negated extensional atoms read under the closed-world assumption over the active domain, and let $I$ be an instance
over its extensional relations. Then

1. $P$ has a unique minimal model $J$ with $J|_{\mathrm{edb}(P)} = I$;
2. $T_P$ has a unique minimal fixpoint $J$ with $J|_{\mathrm{edb}(P)} = I$; and
3. the two coincide and equal the limit of the increasing sequence $T_P^i(I)$.

Here the condition is "restriction equals $I$" rather than "contains $I$", since negation destroys monotonicity.

## Depends on

- [Stratifications and the precedence graph of a Datalog program with negation](stratifications-and-the-precedence-graph.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](../least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Theorem 15.2.2 and Remark 15.2.3 (pp. 377–378), proof left as Exercise 15.7.
