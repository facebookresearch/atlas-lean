# Final count of counting rounds is the frontier weight

Let a branching step and a weight $w$ from states to natural numbers be given, let $d \in \mathbb{N}$
and $s$ a state such that every state in the frontier $F$ of $s$ cut at depth $d$ is terminal. For
every $R \ge 2|F| - 1$, where $|F|$ is the length of $F$, applying $R$ weight-counting rounds to the
pair (stack $[s]$, count $0$) gives the empty stack and the count $\sum_{x \in F} w(x)$, summed over
occurrences.
