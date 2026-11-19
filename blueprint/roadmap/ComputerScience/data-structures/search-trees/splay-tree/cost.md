# Cost of a splay

The cost of splaying $t$ at $x$ is $\max(1, \mathrm{rotations}(x, t))$: the number of
rotations performed, or one if there are none. This is the measure of running time that Sleator
and Tarjan use for splaying: since the number of rotations is the depth $d$ of the node splayed,
the cost $\max(1, d)$ is within a factor two of $1 + d$, and hence proportional to the time of
the search that precedes it.

## Background

- [Number of rotations performed by splaying](rotations.md): the rotation count.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2 ("we use the number of rotations done, unless there are no rotations, in which
  case we charge one for the splaying").
