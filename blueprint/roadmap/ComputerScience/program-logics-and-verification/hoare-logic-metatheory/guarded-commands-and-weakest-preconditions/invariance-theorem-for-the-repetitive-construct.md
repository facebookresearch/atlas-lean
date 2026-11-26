# Invariance theorem for the repetitive construct

Let $DO = \mathbf{do}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{od}$, let $IF$ be the alternative construct with the same guarded commands, and $BB = B_1 \vee \dots \vee B_n$. Let $P$ be a predicate and $t$ an integer-valued function on states such that, in every state,

- $(P \wedge BB) \Rightarrow (\mathrm{wp}(IF, P) \wedge \mathrm{wdec}(IF, t))$, and
- $(P \wedge BB) \Rightarrow t \ge 0$.

Then $P \Rightarrow \mathrm{wp}(DO, P \wedge \neg BB)$ holds in every state. Here $P$ is the *invariant relation* and $t$ the *variant function*. The proof shows by induction on $k$ that $P \wedge t < k$ implies $H_k(P \wedge \neg BB)$ in the definition of $\mathrm{wp}(DO, \cdot)$; the hypotheses are typically established with the [rule for the alternative construct](rule-for-the-alternative-construct.md) and its [variant counterpart](alternative-construct-decreases-a-variant.md).

## Depends on

- [Weakest preconditions of guarded commands](weakest-preconditions-of-guarded-commands.md)

## Related topics

- [Rule for the alternative construct](rule-for-the-alternative-construct.md)
- [The alternative construct decreases a variant](alternative-construct-decreases-a-variant.md)

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Section 3.3, Theorem 3.
