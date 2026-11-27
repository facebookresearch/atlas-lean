# Correctness of the union-find equivalence query

Call two natural numbers $a$ and $c$
equivalent in a union-find structure when they have the same root, where a number that is not a
node is its own root. Let $U$ be a union-find structure with nodes $0, \dots, N-1$ and let
$x, y < N$. The equivalence query on $x$ and $y$, which runs FIND-SET with path compression on
$x$ and then on $y$, returns a union-find structure $U'$ and a boolean $b$ such that $U'$ has
$N$ nodes, $b$ is true if and only if $x$ and $y$ are equivalent in $U$, and for all natural
numbers $a$ and $c$, $a$ and $c$ are equivalent in $U'$ if and only if they are equivalent
in $U$.
