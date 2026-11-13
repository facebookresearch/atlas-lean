# Appending to a heap-ordered array prepares it for sift-up

If an array $a$ of length $n$
over a linearly ordered type is heap-ordered and $x$ is any value, then the array obtained by
appending $x$ to $a$ satisfies the sift-up precondition at index $n$, the position of $x$: the
only edge that may violate heap order is the one entering index $n$.
