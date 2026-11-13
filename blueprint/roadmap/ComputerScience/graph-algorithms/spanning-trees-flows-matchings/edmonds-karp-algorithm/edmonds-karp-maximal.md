# Maximality of the Edmonds–Karp flow

Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be distinct
vertices, and let $f$ be the flow returned by the Edmonds–Karp algorithm on $c$, $s$, $t$.
Then every integer flow $g$ that is feasible for $c$, $s$, $t$ has value at $s$ at most
the value of $f$ at $s$, where the value of a flow at $s$ is its net flow out of $s$.
