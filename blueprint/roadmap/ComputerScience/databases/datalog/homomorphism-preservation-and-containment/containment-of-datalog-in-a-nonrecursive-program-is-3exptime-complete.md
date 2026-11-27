# Containment of a Datalog query in a nonrecursive program is 3EXPTIME-complete

A Datalog program is nonrecursive when the graph on its predicates with an edge from each body predicate to the head
predicate of each rule is acyclic, and linear when every rule has at most one intensional body atom.

**Theorem (Chaudhuri–Vardi).** Containment of a Datalog query in a nonrecursive Datalog query over the same extensional
schema, with output relations of the same arity, is decidable and complete for
3EXPTIME, and complete for 2EXPSPACE when the recursive program is linear. The extra exponential comes from unfolding the
nonrecursive program into a union of conjunctive queries, which can be exponentially larger, and it is unavoidable. All programs here are constant-free: every argument of every atom is a variable, as in the source (§2.1).

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [The class EXPSPACE](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Containment of a Datalog query in a union of conjunctive queries is 2EXPTIME-complete](containment-of-datalog-in-a-ucq-is-2exptime-complete.md)

## Sources

- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Theorem 3.2 and Theorem 6.4 (pp. 8 and 30 of the author copy); §2.1 (p. 4 of the author copy: atoms have only variables as arguments).
