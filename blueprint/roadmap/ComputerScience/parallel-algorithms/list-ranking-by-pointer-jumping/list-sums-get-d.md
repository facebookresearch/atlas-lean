# Pointer jumping computes all suffix sums in $\lceil \log_2 n \rceil$ rounds

Let
$\mathrm{succ}$ be a partial successor function on nodes $0, \dots, n-1$ under which every list
ends, that is, from every node, the node reached in $n$ steps along $\mathrm{succ}$ is undefined,
and let $x_v$ be values in an additive monoid $M$. Then for every node $v$, entry $v$ of the
array of sums computed by $\lceil \log_2 n \rceil$ rounds of pointer jumping on arrays is the
suffix sum of $v$: the sum, in list order, of the values from $v$ to the end of its list.
