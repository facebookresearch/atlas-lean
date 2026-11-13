# Rank of a node in a linked list

Let $\mathrm{succ}$ be a successor map on the nodes
$0, \dots, n-1$ whose lists terminate. The rank of a node $v$ is the least $k$ such that following
$\mathrm{succ}$ for $k + 1$ steps from $v$ runs off the end of the list, that is, the number of
nodes after $v$ in its list.
