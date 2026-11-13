# Edmonds-Karp computes a maximum flow and a minimum cut

Let $c$ be a capacity function on
the vertices $0, \dots, n-1$ with natural-number values, viewed as real capacities, and let
$s \ne t$ be vertices. Let $f$ be the real arc flow of the flow computed by the Edmonds-Karp
algorithm on $c$, $s$, $t$ (its positive part, viewed as real numbers), and let $S_0$ be the set
of vertices reachable from $s$ in the residual graph of that flow. Then $f$ is a feasible $s$-$t$
flow for $c$; every feasible real-valued $s$-$t$ flow for $c$ has value at most the value of $f$;
the value of $f$ is at most the capacity of every $s$-$t$ cut; $S_0$ is an $s$-$t$ cut; and the
value of $f$ equals the capacity of $S_0$.
