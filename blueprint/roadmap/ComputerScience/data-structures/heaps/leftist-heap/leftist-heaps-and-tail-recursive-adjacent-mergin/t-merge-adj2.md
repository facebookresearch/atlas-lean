# Cost of tail-recursive adjacent merging

Over a linear order, the cost of tail-recursive adjacent merging of a list of leftist heaps with
an accumulator $C$ is defined recursively: it is $0$ for the empty list and for a one-heap list,
and for a list $t_1, t_2$ followed by $L$ it is the cost of merging $t_1$ and $t_2$ plus the cost
for $L$ with the accumulator consisting of the merge of $t_1$ and $t_2$ followed by $C$. Only merge
steps are counted; handling the accumulator, including its final reversal, costs nothing.
