# Precondition strengthening for partial correctness

Let $P$, $P'$ and $Q$ be assertions
and $c$ a command. If $P$ entails $P'$ (every state satisfying $P$ satisfies $P'$) and the
partial-correctness triple $\{P'\}\,c\,\{Q\}$ is derivable in the partial-correctness proof
system, then so is $\{P\}\,c\,\{Q\}$.
