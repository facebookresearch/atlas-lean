# Cost recurrence for linear search

For every predicate $p$ on a type $\alpha$, every
$x \in \alpha$ and every list $T$ over $\alpha$, the cost of linear search for $p$ on the list
with head $x$ and tail $T$ is $1$ if $p(x)$ is true, and $1$ plus the cost of linear search for
$p$ on $T$ if $p(x)$ is false. The head costs one evaluation of $p$, and the tail is searched only
when the head fails.
