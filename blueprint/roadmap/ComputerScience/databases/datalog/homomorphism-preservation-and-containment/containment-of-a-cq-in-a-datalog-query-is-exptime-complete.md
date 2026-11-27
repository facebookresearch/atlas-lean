# Containment of a conjunctive query in a Datalog query is EXPTIME-complete

Deciding, given a conjunctive query $q$ and a Datalog query $(P, T)$, whether $q \subseteq (P, T)$ is complete for
EXPTIME. When the arities of the relations of the programs are bounded by a constant, the problem is NP-complete. The
upper bound follows from the [canonical-database test](containment-of-a-cq-in-a-datalog-query-via-the-canonical-database.md);
this complexity is the expression complexity of evaluating Datalog programs. The query and the program are constant-free:
every argument of every atom is a variable, as in Chaudhuri and Vardi (§2.1).

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [The class EXP](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [Containment of a conjunctive query in a Datalog query via the canonical database](containment-of-a-cq-in-a-datalog-query-via-the-canonical-database.md)

## Proof depends on

- [Datalog evaluation is EXPTIME-complete](../datalog-evaluation-is-exptime-complete.md)

## Sources

- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Section 1 (pp. 2–4 of the author copy): EXPTIME-complete, citing earlier work, and NP-complete for programs of bounded arity; §2.1 (p. 4 of the author copy: atoms have only variables as arguments).
