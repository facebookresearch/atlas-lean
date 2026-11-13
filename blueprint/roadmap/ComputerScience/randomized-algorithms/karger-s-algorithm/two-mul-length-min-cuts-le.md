# At most $n(n-1)/2$ minimum cuts

**At most $n(n-1)/2$ minimum cuts** (Karger; Kleinberg and Tardos, Section 13.2). Let $G$ be a
valid multigraph with $n \ge 2$ vertices whose minimum cut size $k$ is at least $1$. If
$X_1, \dots, X_m$ are cuts of $G$, each with exactly $k$ crossing edges, that are pairwise
distinct as partitions of the vertices of $G$, then $2m \le n(n-1)$, that is, $m \le n(n-1)/2$.

Each of these cuts is output by a run of the contraction process with probability at least
$2/(n(n-1))$, and the runs that output distinct partitions are disjoint.
