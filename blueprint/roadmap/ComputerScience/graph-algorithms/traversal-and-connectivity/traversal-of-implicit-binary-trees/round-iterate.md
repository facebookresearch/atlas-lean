# Exact round count for traversing a terminal frontier

Let $k \in \mathbb{N}$ and $s$ a state such that every state in the frontier of $s$ cut at depth
$k$ is terminal, and let $F$ be that frontier, of length $|F|$. For all lists $R$ and $O$ of
states, applying exactly $2|F| - 1$ depth-first rounds to the pair (stack $s$ followed by $R$,
output $O$) gives the pair (stack $R$, output: the reverse of $F$ followed by $O$).

The hypothesis that the frontier is terminal is needed: a depth-cut frontier may contain branching
states.
