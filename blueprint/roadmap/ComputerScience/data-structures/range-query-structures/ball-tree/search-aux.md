# Accumulating ball-tree search

Let $d$ be a dimension and write $\delta(x, y)$ for the
squared distance from $x$ to $y$ in $\mathbb{Z}^d$. For a ball tree $T$ over $\mathbb{Z}^d$, a
query point $q \in \mathbb{Z}^d$, a squared radius $r \in \mathbb{N}$ and a list $A$ of points,
the accumulating search of $T$ for $q$ and $r$ with accumulator $A$ is $A$ when $T$ is empty;
when $T$ is a leaf holding $p$, it is $p$ followed by $A$ if $\delta(q, p) \le r$ and $A$
otherwise; when $T$ is a node with center $c$, squared-radius bound $b$ and children $L$ and $R$,
it is $A$ if $2(b + r) < \delta(c, q)$, and otherwise the accumulating search of $L$ for $q$ and
$r$ whose accumulator is the accumulating search of $R$ for $q$ and $r$ with accumulator $A$.

When $T$ satisfies the bounding-sphere invariant, this pruning is sound by the relaxed triangle
inequality $\delta(x, z) \le 2(\delta(x, y) + \delta(y, z))$ for all $x, y, z \in \mathbb{Z}^d$,
and the result is the points of $T$ within squared distance $r$ of $q$, from left to right,
followed by $A$.
