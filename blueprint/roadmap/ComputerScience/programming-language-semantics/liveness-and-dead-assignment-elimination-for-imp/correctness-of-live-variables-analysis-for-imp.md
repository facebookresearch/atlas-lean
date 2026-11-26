# Correctness of live-variables analysis for IMP

Write $s = t$ on $Y$ when the [states](../operational-semantics-of-imp/state.md) $s$ and $t$ agree on every variable in $Y$, and let $L(c, X)$ be the set of [live variables](live-variables-of-an-imp-command.md) before the command $c$ relative to $X$.

**Theorem.** If $c$ takes $s$ to $s'$ in the [big-step semantics](../operational-semantics-of-imp/big-step.md) and $s = t$ on $L(c, X)$, then there is a state $t'$ such that $c$ takes $t$ to $t'$ and $s' = t'$ on $X$.

So the final values of the variables in $X$ depend only on the initial values of the variables in $L(c, X)$, and running $c$ from a state that agrees with $s$ there also terminates.

**Proof.** By rule induction on the big-step derivation, generalizing over $t$.
- *Coincidence.* An expression evaluates to the same value in two states that agree on its variables; this settles the assignment case and the evaluation of conditions, whose variables are included in $L$.
- *Loops.* The case of a loop whose condition is true uses that $L(\mathtt{while}\ b\ \mathtt{do}\ c, X)$ contains $\mathrm{vars}(b)$ and $X$, and contains $L(c, L(\mathtt{while}\ b\ \mathtt{do}\ c, X))$. The last inclusion holds because $L(c, Y) = \mathit{gen}(c) \cup (Y \setminus \mathit{kill}(c))$ for sets $\mathit{gen}(c)$ and $\mathit{kill}(c)$ that do not depend on $Y$.

## Depends on

- [Big-step semantics of IMP](../operational-semantics-of-imp/big-step.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [IMP program states](../operational-semantics-of-imp/state.md)

## Proof depends on

- [Coincidence for IMP expressions](coincidence-for-imp-expressions.md)
- [Live variables of a loop are closed under its body](live-variables-of-a-loop-are-closed-under-its.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3: Lemma 10.15 (liveness via gen/kill), Lemma 10.16, Lemma 10.17 (coincidence), and Theorem 10.18 (correctness of $L$) with its proof by rule induction and Figure 10.7.
