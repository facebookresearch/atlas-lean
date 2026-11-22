# Correctness of Johnson's algorithm

Let $E$ be a list of directed edges on the vertices
$\{0, \dots, n-1\}$ with integer weights, and suppose Johnson's algorithm on $E$ returns a
table $d$. Then for all vertices $s$ and $t$, $d(s, t) = \infty$ if and only if $t$ is not
reachable from $s$ along edges of $E$. Moreover, if $d(s, t)$ is an integer $x$, then some
weighted path in $E$ from $s$ to $t$ has weight $x$, and every weighted path in $E$ from $s$ to
$t$ has weight at least $x$.
