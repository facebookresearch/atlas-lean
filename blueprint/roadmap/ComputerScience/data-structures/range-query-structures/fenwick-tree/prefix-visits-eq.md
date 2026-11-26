# One step of the Fenwick prefix walk

For natural array length $n$ and
requested length $k$, let $j=\min(k,n)$. The visit list is empty if $j=0$. Otherwise it
starts with $j$, followed by the prefix visits at length $j-\operatorname{lowbit}(j)$
in the same array.
