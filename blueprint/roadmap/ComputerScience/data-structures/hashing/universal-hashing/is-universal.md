# Universal hash family

A finite family $H$ of functions from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$ is universal if $m > 0$, $H$ is nonempty, and for all distinct keys
$x \ne y$ in $\alpha$ the number of functions $h \in H$ with $h(x) = h(y)$, multiplied by $m$,
is at most $|H|$; that is, $x$ and $y$ collide under at most a $1/m$ fraction of the members
of $H$.

Nonemptiness makes sense of choosing a member of $H$ uniformly at random, the reading behind
the bound.
