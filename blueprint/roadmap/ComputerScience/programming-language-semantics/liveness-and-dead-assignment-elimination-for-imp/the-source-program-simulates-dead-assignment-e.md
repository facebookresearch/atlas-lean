# The source program simulates dead-assignment elimination

Let $L$ be [liveness](live-variables-of-an-imp-command.md) and $\mathrm{bury}$ [dead-assignment elimination](dead-assignment-elimination-for-imp.md), write $s = t$ on $Y$ when the states agree on $Y$, and take "takes $s$ to $s'$" in the [big-step semantics](../operational-semantics-of-imp/big-step.md). If $\mathrm{bury}(c, X)$ takes $s$ to $s'$ and $s = t$ on $L(c, X)$, then $c$ takes $t$ to some $t'$ with $s' = t'$ on $X$.

**Proof idea.** Rule induction on the derivation for $\mathrm{bury}(c, X)$, inverting $\mathrm{bury}$ in each case: a sequential composition comes from a sequential composition, and $\mathtt{skip}$ comes from $\mathtt{skip}$ or from an assignment to a variable outside $X$.

## Depends on

- [Dead-assignment elimination for IMP](dead-assignment-elimination-for-imp.md)
- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)

## Proof depends on

- [Coincidence for IMP expressions](coincidence-for-imp-expressions.md)
- [Live variables of a loop are closed under its body](live-variables-of-a-loop-are-closed-under-its.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.3, Lemma 10.20 (correctness of $\mathrm{bury}$, part 2) with its proof and Figure 10.8.
