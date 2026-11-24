# Fisher–Yates output is a rearrangement of its input

For every vector $x$ of length $n$
and every draw history $d$, which assigns to each position $i < n$ a number $d_i$ with
$0 \le d_i < n - i$, the list of entries of the vector returned by the Fisher–Yates computation on
$x$ and $d$ is a permutation of the list of entries of $x$. In particular every value occurs
equally often in both, even when values of $x$ repeat.
