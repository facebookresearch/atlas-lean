# Soundness of the verification precondition for the imperative language with arrays

Let $\mathrm{pre}(c, Q)$ be the verification precondition of a statement $c$ for a postcondition $Q$, computed by recursion on $c$ from its loop invariants and requiring every read to be in bounds. For every statement $c$, predicate $Q$ on states and states $s$ and $s'$: if $\mathrm{pre}(c, Q)(s)$ holds and $c$ takes $s$ to $s'$ in the big-step semantics, then $Q(s')$ holds. This is partial correctness only.
