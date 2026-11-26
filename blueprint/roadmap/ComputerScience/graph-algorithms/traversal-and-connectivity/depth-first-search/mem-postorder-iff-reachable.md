# Depth-first search finishes exactly the reachable vertices

Let $G$ be a finite directed
graph and $R$ a list of root vertices. A vertex $v$ occurs in the finish order (postorder) of the
depth-first search of $G$ from $R$ if and only if there is a root $r$ in $R$ from which $v$ is
reachable in $G$ by a directed path of length zero or more.
