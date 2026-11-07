# Exact subset sum returns the maximum of the computed sums

For every list $x$ of natural
numbers and every natural number $t$, the value returned by the exact subset sum algorithm on $x$
with target $t$ equals $\max(\cdots\max(\max(0, s_1), s_2)\cdots, s_k)$, where $s_1, \dots, s_k$
is the final list of sums computed by the exact subset sum traversal on $x$ with target $t$.
