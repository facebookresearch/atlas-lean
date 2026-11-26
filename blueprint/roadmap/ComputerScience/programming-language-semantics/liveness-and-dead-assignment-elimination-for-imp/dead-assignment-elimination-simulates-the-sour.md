# Dead-assignment elimination simulates the source program

Let $L$ be [liveness](live-variables-of-an-imp-command.md) and $\mathrm{bury}$ [dead-assignment elimination](dead-assignment-elimination-for-imp.md), write $s = t$ on $Y$ when the states agree on $Y$, and take "takes $s$ to $s'$" in the [big-step semantics](../operational-semantics-of-imp/big-step.md). If $c$ takes $s$ to $s'$ and $s = t$ on $L(c, X)$, then $\mathrm{bury}(c, X)$ takes $t$ to some $t'$ with $s' = t'$ on $X$.

**Proof idea.** Rule induction on the derivation for $c$, as for the [correctness of live-variables analysis](correctness-of-live-variables-analysis-for-imp.md); an assignment to a variable outside $X$ becomes $\mathtt{skip}$, which leaves the agreement on $X$ intact.

## Depends on

- [Dead-assignment elimination for IMP](dead-assignment-elimination-for-imp.md)
- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)

## Proof depends on

- [Coincidence for IMP expressions](coincidence-for-imp-expressions.md)
- [Live variables of a loop are closed under its body](live-variables-of-a-loop-are-closed-under-its.md)
- [Correctness of live-variables analysis for IMP](correctness-of-live-variables-analysis-for-imp.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.3, Lemma 10.19 (correctness of $\mathrm{bury}$, part 1) and Figure 10.8.
