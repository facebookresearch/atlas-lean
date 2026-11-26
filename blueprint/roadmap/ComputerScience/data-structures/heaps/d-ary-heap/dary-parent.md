# Parent index in a $d$-ary tree

For natural numbers $d$ and $i$, the $d$-ary parent of $i$
is $\lfloor (i - 1)/d \rfloor$, computed in the natural numbers: $i - 1$ is truncated at $0$, so
the parent of $0$ is $0$, and division by $0$ gives $0$.

This is the parent index when a $d$-ary tree is stored in level order in an array with its root
at index $0$.
