# Enough rounds empty the stack and collect the frontier

Let $k \in \mathbb{N}$ and $s$ a state such that every state in the frontier $F$ of $s$ cut at
depth $k$ is terminal. For every $R \ge 2|F| - 1$, where $|F|$ is the length of $F$, applying $R$
depth-first rounds to the pair (stack $[s]$, empty output) gives the empty stack and the reverse
of $F$ as output.
