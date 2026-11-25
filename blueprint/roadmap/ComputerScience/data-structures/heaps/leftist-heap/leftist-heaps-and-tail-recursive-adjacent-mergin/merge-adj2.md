# Tail-recursive adjacent merging with an accumulator

Over a linear order, tail-recursive adjacent merging of a list of leftist heaps with an
accumulator list $C$ is defined recursively: for the empty list the result is the reverse of $C$;
for a one-heap list $[t]$ it is the reverse of the list whose first heap is $t$ and whose
remaining heaps are those of $C$, that is, the reverse of $C$ followed by the heap $t$; for a list $t_1, t_2$ followed
by $L$ it is the tail-recursive adjacent merging of $L$ with the accumulator consisting of the
merge of $t_1$ and $t_2$ followed by $C$.
