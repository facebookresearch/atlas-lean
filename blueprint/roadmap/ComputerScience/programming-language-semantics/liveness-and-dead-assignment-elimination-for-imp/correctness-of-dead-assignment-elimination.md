# Correctness of dead-assignment elimination

Let $\mathrm{bury}$ be [dead-assignment elimination](dead-assignment-elimination-for-imp.md) and take "takes $s$ to $s'$" in the [big-step semantics](../operational-semantics-of-imp/big-step.md). With $X$ the set of all variables, $\mathrm{bury}(c, X)$ and $c$ are equivalent: for all states $s$ and $s'$, $\mathrm{bury}(c, X)$ takes $s$ to $s'$ if and only if $c$ takes $s$ to $s'$.

**Proof.** Apply [the forward simulation](dead-assignment-elimination-simulates-the-sour.md) and [the backward simulation](the-source-program-simulates-dead-assignment-e.md) with $t = s$; states that agree on every variable are equal.

Elimination is not idempotent: applying it to its own result can remove further assignments.

## Depends on

- [Dead-assignment elimination for IMP](dead-assignment-elimination-for-imp.md)
- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)

## Proof depends on

- [Dead-assignment elimination simulates the source program](dead-assignment-elimination-simulates-the-sour.md)
- [The source program simulates dead-assignment elimination](the-source-program-simulates-dead-assignment-e.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.3, Corollary 10.21 ($\mathrm{bury}\ c\ \mathrm{UNIV} \sim c$), and Exercise 10.8 (non-idempotence).
