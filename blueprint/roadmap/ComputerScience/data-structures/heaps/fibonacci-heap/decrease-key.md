# Decrease-key in a Fibonacci heap

Given a Fibonacci heap $H$ over a linearly ordered type,
a root index $i$, a path $p$ of child indices and a key $k$, decrease-key cuts the subtree $S$ at
path $p$ out of the $i$-th tree of the root list of $H$, replaces the root of $S$ by $k$, and
puts the resulting tree in front of the remaining forest (the root list with the $i$-th tree
replaced by what is left of it after the cut, or removed when $S$ is that whole tree). The
cached minimum of the result is the smaller of $k$ and the previous cached minimum, computed
without rescanning the root list. When the cut fails (the address does not resolve) or $k$ is
greater than the root of $S$, the heap $H$ is returned unchanged.

Unlike CLRS decrease-key, this performs no cascading cuts: the trees carry no mark field.
