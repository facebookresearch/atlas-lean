# Search of a built ball tree

Let $L$ be a list of points of $\mathbb{Z}^d$, let
$q, p \in \mathbb{Z}^d$ and let $r$ be a natural number. Then $p$ is returned by the similarity
search with query $q$ and squared radius $r$ on the ball tree built from $L$ if and only if $p$
occurs in $L$ and the squared distance from $q$ to $p$ is at most $r$.
