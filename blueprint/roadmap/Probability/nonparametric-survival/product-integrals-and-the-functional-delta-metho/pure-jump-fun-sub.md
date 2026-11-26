# Increments of a pure-jump integrator

Let $T$ be a finite index set and $s, a$ real functions on the indices. The [pure-jump integrator](pure-jump-fun.md) with jumps $a_j$ at the times $s_j$ is

$$
J(t) = \sum_{j \in T,\ s_j \le t} a_j, \qquad t \in \mathbb{R}.
$$

For all reals $y \le x$,

$$
J(x) - J(y) = \sum_{j \in T,\ y < s_j \le x} a_j.
$$
