# The repetitive construct preserves an invariant

Let $DO = \mathbf{do}\ B_1 \to SL_1 \mathbin{[\!]} \cdots \mathbin{[\!]} B_n \to SL_n\ \mathbf{od}$, let $IF$ be the alternative construct with the same guarded commands, and $BB = B_1 \vee \dots \vee B_n$. If $(P \wedge BB) \Rightarrow \mathrm{wp}(IF, P)$ holds in every state, then

$$(P \wedge \mathrm{wp}(DO, T)) \Rightarrow \mathrm{wp}(DO, P \wedge \neg BB)$$

holds in every state. Thus an invariant of the guarded lists holds on termination, from every initial state satisfying it from which $DO$ is guaranteed to terminate.

## Depends on

- [Weakest preconditions of guarded commands](weakest-preconditions-of-guarded-commands.md)

## Sources

- E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs", *Communications of the ACM* 18(8):453–457, 1975; author's manuscript EWD472, <https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF>, Section 3.3, Theorem 4.
