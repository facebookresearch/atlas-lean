# Lineage blocks after the first coalescence events

For a [ranked labeled history](ranked-history.md) $h$ of $n$ genes and a natural number $t$, the list of lineages after the first $t$ coalescence events of $h$, each lineage given as its block of sampled genes and listed by lineage label: starting from the singletons $\{0\}, \dots, \{n-1\}$, the events of steps $0, 1, \dots, \min(t, n-1) - 1$ are applied in turn, the event recording the pair $\{a, b\}$ with $a < b$ [merging the blocks](merge-blocks.md) at positions $a$ and $b$.
