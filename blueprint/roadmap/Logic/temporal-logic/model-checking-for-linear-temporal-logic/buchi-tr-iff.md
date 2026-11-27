# Büchi transition test via the computable counter update

The Büchi automaton of an LTL formula $\varphi$ has a transition from $(s, i)$ to $(t, j)$ on a
letter $x$, where $s, t$ are tableau states and $i, j$ fairness counters, if and only if the tableau
step from $s$ to $t$ on $x$ holds and $j$ is the counter obtained from $i$ by the fairness update at
$t$.
