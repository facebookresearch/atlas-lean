# Indexed walk

In an edge-indexed multigraph, an indexed walk is a walk that records which
edge it traverses at each step. Indexed walks are defined inductively: for every vertex $v$ there
is the empty indexed walk from $v$ to $v$, and if $e$ is an edge with endpoints $u$ and $v$ and
$p$ is an indexed walk from $v$ to $w$, then traversing $e$ from $u$ to $v$ and then following
$p$ is an indexed walk from $u$ to $w$.
