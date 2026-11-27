# Correctness of true liveness

Let $L_t(c, X)$ be the set of [truly live variables](true-liveness-of-an-imp-command.md) before an IMP command $c$ relative to $X$, write $s = t$ on $Y$ when the states $s$ and $t$ agree on $Y$, and take "takes $s$ to $s'$" in the [big-step semantics](../operational-semantics-of-imp/big-step.md).

**Theorem.**
1. If $c$ takes $s$ to $s'$ and $s = t$ on $L_t(c, X)$, then $c$ takes $t$ to some $t'$ with $s' = t'$ on $X$.
2. Let $\mathrm{bury}_t$ be [dead-assignment elimination](dead-assignment-elimination-for-imp.md) with $L_t$ in place of $L$. If $c$ takes $s$ to $s'$ and $s = t$ on $L_t(c, X)$, then $\mathrm{bury}_t(c, X)$ takes $t$ to some $t'$ with $s' = t'$ on $X$; and if $\mathrm{bury}_t(c, X)$ takes $s$ to $s'$ and $s = t$ on $L_t(c, X)$, then $c$ takes $t$ to some $t'$ with $s' = t'$ on $X$. So with $X$ the set of all variables, $\mathrm{bury}_t(c, X)$ and $c$ take each state to the same final states.

**Proof.** As for [live-variables analysis](correctness-of-live-variables-analysis-for-imp.md), by rule induction on the big-step derivation. The loop case uses only the inclusions $\mathrm{vars}(b) \subseteq L_t(w, X)$, $X \subseteq L_t(w, X)$ and $L_t(c, L_t(w, X)) \subseteq L_t(w, X)$ for $w = \mathtt{while}\ b\ \mathtt{do}\ c$, which hold because the least fixed point is a fixed point. The assignment case $x := a$ with $x \notin X$ holds because the assignment changes only $x$, which is outside $X$.

## Depends on

- [True liveness of an IMP command](true-liveness-of-an-imp-command.md)
- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)
- [Dead-assignment elimination for IMP](dead-assignment-elimination-for-imp.md)

## Proof depends on

- [True liveness is monotone](true-liveness-is-monotone.md)
- [Coincidence for IMP expressions](coincidence-for-imp-expressions.md)
- [Dead-assignment elimination simulates the source program](dead-assignment-elimination-simulates-the-sour.md)
- [The source program simulates dead-assignment elimination](the-source-program-simulates-dead-assignment-e.md)
- [Correctness of live-variables analysis for IMP](correctness-of-live-variables-analysis-for-imp.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.4: Lemma 10.31 (correctness of the modified $L$, whose loop case relies only on the pre-fixpoint constraints) and the remark that $\mathrm{bury}$ and its correctness proof carry over verbatim to true liveness.
