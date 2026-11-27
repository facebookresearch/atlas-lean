# Bottleneck augmentation preserves feasibility

Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be vertices,
and let $f$ be a flow that is feasible for $c$, $s$, $t$. If $P$ is a path from $s$ to $t$
in the residual graph of $f$, that is, a nonempty list of pairwise distinct vertices
starting at $s$ and ending at $t$ whose consecutive pairs are residual edges, then the
augmentation of $f$ along $P$ by the bottleneck of $P$ is again feasible for $c$, $s$,
$t$.
