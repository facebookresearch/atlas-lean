# Correctness of insertion into an indexed interval tree

Let $T$ be an indexed interval tree
satisfying the representation invariant, and let $x$ be an entry whose interval is valid (its low
endpoint is at most its high endpoint). If inserting $x$ into $T$ succeeds with result $T'$, then
$T'$ satisfies the representation invariant, $x$ is stored in the root tree of $T'$, and an entry
$e$ is stored in the root tree of $T'$ if and only if either $e = x$, or $e$ is stored in the root
tree of $T$ and the identifier of $e$ differs from the identifier of $x$.
