# Equivalence of a Datalog query to a nonrecursive program is 3EXPTIME-complete

A Datalog program is nonrecursive when the graph on its predicates with an edge from each body predicate to the head
predicate of each rule is acyclic, and linear when every rule has at most one intensional body atom.

**Theorem (Chaudhuri–Vardi).** Deciding whether a given Datalog query is equivalent to a given nonrecursive Datalog query is
decidable and complete for 3EXPTIME (2EXPSPACE for linear recursive programs). If the nonrecursive program is also linear,
the problem is complete for 2EXPTIME (EXPSPACE for linear recursive programs). This differs from the boundedness problem,
whether a program is equivalent to some nonrecursive program, which is undecidable.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Containment of a Datalog query in a nonrecursive program is 3EXPTIME-complete](containment-of-datalog-in-a-nonrecursive-program-is-3exptime-complete.md)
- [Containment of a Datalog query in a union of conjunctive queries is 2EXPTIME-complete](containment-of-datalog-in-a-ucq-is-2exptime-complete.md)

## Informally uses

- [Boundedness of Datalog is undecidable](../boundedness-of-datalog-is-undecidable.md)

## Sources

- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Corollary 3.3, Theorem 6.5 and Theorem 6.7 (pp. 9 and 31 of the author copy).
