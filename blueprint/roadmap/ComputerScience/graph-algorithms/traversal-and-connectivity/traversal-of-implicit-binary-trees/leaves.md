# Depth-cut frontier of a binary branching step

Let a branching step on a set $S$ of states assign to each state $s$ either nothing ($s$ is
terminal) or an ordered pair $(l, h)$ of children. The frontier of $s$ cut at depth $k$ is the
list defined by recursion on $k$: at depth $0$ it is $[s]$, even when $s$ branches; at depth
$k + 1$ it is $[s]$ if $s$ is terminal, and the frontier of $l$ cut at depth $k$ followed by the
frontier of $h$ cut at depth $k$ if $s$ branches into $(l, h)$. The frontier lists states from left
to right and keeps repeated occurrences.
