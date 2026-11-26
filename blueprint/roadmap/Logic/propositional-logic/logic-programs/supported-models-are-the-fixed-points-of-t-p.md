# Supported models are the fixed points of the immediate-consequence operator

Let $P$ be a [finite ground normal logic program](normal-logic-program.md) with [immediate-consequence operator](immediate-consequence-operator-of-a-normal-program.md) $T_P$, and let $I$ be an interpretation.

1. $I$ is [supported](supported-models.md) by $P$ if and only if $I \subseteq T_P(I)$.
2. $I$ is a supported model of $P$ if and only if $T_P(I) = I$.

**Proof.** Part 1 restates the definitions: $a \in T_P(I)$ says that $a$ is the head of a rule whose body is true in $I$. Part 2 combines part 1 with the fact that the [models are the pre-fixed points](models-are-the-pre-fixed-points-of-t-p.md) of $T_P$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Supported models](supported-models.md)
- [Immediate-consequence operator of a normal program](immediate-consequence-operator-of-a-normal-program.md)

## Proof depends on

- [Models are the pre-fixed points of the immediate-consequence operator](models-are-the-pre-fixed-points-of-t-p.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Proposition 2.19 and its proof.
