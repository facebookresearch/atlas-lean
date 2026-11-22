# Cost of non-tail-recursive adjacent merging

Over a linear order, the cost of adjacent merging of a list of leftist heaps is defined
recursively: it is $0$ for the empty list and for a one-heap list, and for a list $t_1, t_2$
followed by $L$ it is the cost of merging $t_1$ and $t_2$ plus the cost of adjacent merging of
$L$. Only merge steps are counted.
