# Precondition strengthening for total correctness

Let $P$, $P'$ and $Q$ be assertions and
$c$ a command. If $P$ entails $P'$ (every state satisfying $P$ satisfies $P'$) and the triple
$\{P'\}\,c\,\{Q\}$ is derivable in total-correctness Hoare logic, then so is
$\{P\}\,c\,\{Q\}$.
