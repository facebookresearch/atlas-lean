# Stable three-way partition

Let $p$ be an element of a linearly ordered type $\alpha$. The
three-way partition of a list over $\alpha$ around $p$, together with the time it is charged, is
defined by recursion on the list. The empty list gives three empty lists at no cost. For a list
with head $x$ and tail $xs$, one unit of time is charged for comparing $x$ with $p$, the tail $xs$
is partitioned, and $x$ is put at the front of its below list if $x < p$, of its equal list if
$x = p$, and of its above list if $p < x$.
