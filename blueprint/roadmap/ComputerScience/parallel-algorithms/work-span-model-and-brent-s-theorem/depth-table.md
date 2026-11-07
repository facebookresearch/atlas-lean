# Table of depths

The list of the depths of tasks $0, \dots, n - 1$ of a computation DAG on
$n$ tasks, computed once each in topological order: the entry for task $k$ is $1$ plus the largest
entry at a predecessor of $k$, or $1$ if $k$ has no predecessors.

With lists (appending and indexed reads take linear time) this costs $O(n^2 + n|E|)$, where $|E|$
is the total number of predecessor entries; evaluating the depth directly from its recursive
definition instead recomputes shared subpaths exponentially often.
