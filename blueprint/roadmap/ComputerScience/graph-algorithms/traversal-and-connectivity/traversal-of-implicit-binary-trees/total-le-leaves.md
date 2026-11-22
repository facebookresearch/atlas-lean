# Pending plus collected occurrences are bounded by the frontier length

Let $d \in \mathbb{N}$ and $s$ a state such that every state in the frontier of $s$ cut at depth
$d$ is terminal. Then for every $i \in \mathbb{N}$, after $i$ depth-first rounds from the pair
(stack $[s]$, empty output), the length of the stack plus the length of the output is at most the
length of that frontier.
