# Containment of a Datalog query in a union of conjunctive queries is 2EXPTIME-complete

A Datalog program is nonrecursive when the graph on its predicates with an edge from each body predicate to the head
predicate of each rule is acyclic, and linear when every rule has at most one intensional body atom.

**Theorem (Chaudhuri–Vardi).** Deciding, given a Datalog query $(P, Q)$ and a union of conjunctive queries $\psi$ of the
same arity over its extensional schema, whether $(P, Q) \subseteq \psi$ is complete for 2EXPTIME, and complete for EXPSPACE
when $P$ is linear, completeness being under polynomial-time many-one reductions. The lower bounds hold even for programs of bounded arity. The proof views $P$ as the infinite union of
its expansion trees and reduces containment to containment of tree automata of exponential size.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [Containment of unions of conjunctive queries](../../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)
- [The class EXPSPACE](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/expspace.md)
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Datalog queries are equivalent to infinitary unions of conjunctive queries](datalog-queries-are-equivalent-to-infinitary-ucqs.md)
- [Containment of unions of conjunctive queries](../../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)

## Sources

- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Theorem 5.8, Theorem 5.12 and Theorem 5.15 (pp. 15, 19 and 26 of the author copy).
