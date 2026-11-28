# Models are the pre-fixed points of the immediate-consequence operator

Let $P$ be a [finite ground normal logic program](normal-logic-program.md) with [immediate-consequence operator](immediate-consequence-operator-of-a-normal-program.md) $T_P$. An interpretation $I$ is a [model](models-of-a-normal-logic-program.md) of $P$ if and only if $T_P(I) \subseteq I$.

**Proof.** Both sides say that the head of every rule whose body is true in $I$ belongs to $I$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Models of a normal logic program](models-of-a-normal-logic-program.md)
- [Immediate-consequence operator of a normal program](immediate-consequence-operator-of-a-normal-program.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Proposition 2.5.
