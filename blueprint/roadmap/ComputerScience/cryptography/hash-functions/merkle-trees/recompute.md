# Recomputing a root from a path

Recomputing for $k$ levels starts from a node $c$ at position $i$ of a level with $n$ nodes and a path
$p$. At an odd position the next path entry $s$ is hashed on the left, giving $h(s, c)$; at an even
position with a right neighbour it is hashed on the right, giving $h(c, s)$; at an even last position
the node is promoted and no entry is used. The process continues from position $\lfloor i/2 \rfloor$
of a level with $\lceil n/2 \rceil$ nodes. It fails if the path runs out early or is not used up
exactly.
