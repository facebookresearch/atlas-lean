# Mem component

For a union-find state $u$ and a node $r$, the component of $r$ is the set of allocated nodes whose canonical root is $r$: for every $i$, $i$ belongs to the component of $r$ if and only if $i < |u|$ and the root of $i$ in $u$ is $r$.
