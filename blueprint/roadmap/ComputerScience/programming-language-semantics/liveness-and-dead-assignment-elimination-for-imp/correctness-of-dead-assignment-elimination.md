# Correctness of dead-assignment elimination

Let $L(c, X)$ be the set of [live variables](live-variables-of-an-imp-command.md) before an IMP command $c$ relative to $X$. Dead-assignment elimination $\mathrm{bury}(c, X)$ replaces by $\mathtt{skip}$ every assignment whose target is dead after it:

$$
\begin{aligned}
\mathrm{bury}(\mathtt{skip}, X) &= \mathtt{skip},\\
\mathrm{bury}(x := a, X) &= x := a \text{ if } x \in X, \text{ and } \mathtt{skip} \text{ otherwise},\\
\mathrm{bury}(c_1 ; c_2, X) &= \mathrm{bury}(c_1, L(c_2, X)) ; \mathrm{bury}(c_2, X),\\
\mathrm{bury}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, X) &= \mathtt{if}\ b\ \mathtt{then}\ \mathrm{bury}(c_1, X)\ \mathtt{else}\ \mathrm{bury}(c_2, X),\\
\mathrm{bury}(\mathtt{while}\ b\ \mathtt{do}\ c, X) &= \mathtt{while}\ b\ \mathtt{do}\ \mathrm{bury}(c, L(\mathtt{while}\ b\ \mathtt{do}\ c, X)).
\end{aligned}
$$

Write $s = t$ on $Y$ when the states $s$ and $t$ agree on $Y$, and take "takes $s$ to $s'$" in the [big-step semantics](../operational-semantics-of-imp/big-step.md).

**Theorem.**
1. If $c$ takes $s$ to $s'$ and $s = t$ on $L(c, X)$, then $\mathrm{bury}(c, X)$ takes $t$ to some $t'$ with $s' = t'$ on $X$.
2. If $\mathrm{bury}(c, X)$ takes $s$ to $s'$ and $s = t$ on $L(c, X)$, then $c$ takes $t$ to some $t'$ with $s' = t'$ on $X$.
3. Consequently, with $X$ the set of all variables, $\mathrm{bury}(c, X)$ and $c$ are equivalent: for all states $s$ and $s'$, $\mathrm{bury}(c, X)$ takes $s$ to $s'$ if and only if $c$ takes $s$ to $s'$.

Part 3 follows from parts 1 and 2 with $t = s$, since states that agree on every variable are equal. Parts 1 and 2 are proved by rule induction, like the [correctness of live-variables analysis](correctness-of-live-variables-analysis-for-imp.md); part 2 inverts $\mathrm{bury}$, whose result has the shape of its argument except that $\mathtt{skip}$ may come from an assignment. Elimination is not idempotent: applying it to its own result can remove further assignments.

## Depends on

- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [Correctness of live-variables analysis for IMP](correctness-of-live-variables-analysis-for-imp.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3: the definition of $\mathrm{bury}$, Lemma 10.19 and Lemma 10.20 (the two directions of correctness, Figure 10.8), Corollary 10.21 ($\mathrm{bury}\ c\ \mathrm{UNIV} \sim c$), and Exercise 10.8 (non-idempotence).
