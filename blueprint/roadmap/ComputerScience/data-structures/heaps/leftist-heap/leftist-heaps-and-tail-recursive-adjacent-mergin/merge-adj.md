# Non-tail-recursive adjacent merging of heaps

Over a linear order, adjacent merging of a list of leftist heaps is defined recursively: the empty
list gives the empty list, a one-heap list $[t]$ gives $[t]$, and a list $t_1, t_2$ followed by $L$
gives the merge of $t_1$ and $t_2$ followed by the adjacent merging of $L$.
