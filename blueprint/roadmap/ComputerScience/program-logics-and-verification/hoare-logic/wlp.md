# Weakest liberal precondition

For a command $c$ and an assertion $Q$, the weakest
liberal precondition of $c$ with respect to $Q$ is the assertion that holds in a state $s$
exactly when every state $t$ in which an execution of $c$ from $s$ terminates, under the
big-step semantics, satisfies $Q$.

It is liberal because no termination claim is made: a state from which $c$ has no terminating
execution satisfies it for every $Q$.
