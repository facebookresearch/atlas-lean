# A built kd-tree holds the same points as its input

Let $d \ge 1$, let
$a \in \{0, \dots, d-1\}$ and let $P$ be a list of points in $\mathbb{Z}^d$. A point
$p \in \mathbb{Z}^d$ is stored in the kd-tree built from $P$ by median splits starting at axis
$a$ if and only if $p$ occurs in $P$.
