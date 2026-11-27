# Connectivity by a newest-first edge list

Connectivity of vertices $u$ and $v$ of
$\{0, \dots, n-1\}$ by a list of validated edges, read newest first, is defined by recursion
on the list. By the empty list, $u$ and $v$ are connected exactly when $u = v$. By a list
whose first edge $e$ has source $a$ and target $b$ and whose remaining edges form the list
$L$, the vertices $u$ and $v$ are connected when $u$ and $v$ are connected by $L$, or $u$ is
connected to $a$ and $v$ is connected to $b$ by $L$, or $u$ is connected to $b$ and $v$ is
connected to $a$ by $L$.
