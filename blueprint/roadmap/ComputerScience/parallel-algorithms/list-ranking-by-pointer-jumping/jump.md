# Iterated successor

For a successor map $\mathrm{succ}$ on the nodes $0, \dots, n-1$, where
$\mathrm{succ}(v)$ is either a node or undefined, the $k$-step jump from $v$ is the node reached by
applying $\mathrm{succ}$ $k$ times starting at $v$, and is undefined if some step is undefined: the
$0$-step jump from $v$ is $v$, and the $(k+1)$-step jump is $\mathrm{succ}$ of the $k$-step jump.
