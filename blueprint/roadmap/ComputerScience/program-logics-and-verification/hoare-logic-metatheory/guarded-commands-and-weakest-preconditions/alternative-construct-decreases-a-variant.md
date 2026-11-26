# The alternative construct decreases a variant

Let $IF = \mathbf{if}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{fi}$ and $BB = B_1 \vee \dots \vee B_n$, let $Q$ be a predicate and $t$ an integer-valued function on states. If $(Q \wedge B_i) \Rightarrow \mathrm{wdec}(SL_i, t)$ holds in every state for every $i \in \{1, \dots, n\}$, then $(Q \wedge BB) \Rightarrow \mathrm{wdec}(IF, t)$ holds in every state, where $\mathrm{wdec}(S, t)$ is the weakest precondition guaranteeing that $S$ terminates properly with the value of $t$ decreased by at least $1$.

## Depends on

- [Weakest preconditions of guarded commands](weakest-preconditions-of-guarded-commands.md)

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Section 3.2, Theorem 2.
