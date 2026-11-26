# Rule for the alternative construct

Let $IF = \mathbf{if}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{fi}$ and $BB = B_1 \vee \dots \vee B_n$, and let $Q$ and $R$ be predicates. If $(Q \wedge B_i) \Rightarrow \mathrm{wp}(SL_i, R)$ holds in every state for every $i \in \{1, \dots, n\}$, then $(Q \wedge BB) \Rightarrow \mathrm{wp}(IF, R)$ holds in every state.

The proof is a direct substitution into the clause for $\mathrm{wp}(IF, R)$.

## Depends on

- [Weakest preconditions of guarded commands](weakest-preconditions-of-guarded-commands.md)

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Section 3.2, Theorem 1.
