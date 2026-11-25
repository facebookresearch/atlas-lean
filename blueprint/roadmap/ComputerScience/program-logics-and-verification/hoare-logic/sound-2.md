# Soundness of total-correctness Hoare logic

For all assertions $P$ and $Q$ and every
command $c$, if the triple $\{P\}\,c\,\{Q\}$ is derivable in total-correctness Hoare logic, then
it is valid for total correctness: every state satisfying $P$ has a terminating big-step
execution of $c$ ending in a state that satisfies $Q$.
