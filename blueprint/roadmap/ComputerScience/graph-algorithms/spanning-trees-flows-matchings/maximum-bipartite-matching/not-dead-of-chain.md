# Shortest chains avoiding earlier paths contain no dead vertex

Let $\mu$ be a partner
array, $U$ a set of left vertices and $D$ a set of right vertices, and let $L$ be a set of left
vertices and $R$ a set of right vertices such that every vertex of $U$ lies in $L$ and every
vertex of $D$ lies in $R$ or has no escape avoiding $U$ and $D$. Let $m \in \mathbb{N}$, let $z$ be
a right vertex first reached in round $m + 1$ of the alternating layered search for $\mu$, and let
$S$ be an alternating chain from $z$ with $m + 1$ pairs such that no left vertex of $S$ lies in $L$
and no right vertex of $S$ lies in $R$. Then no right vertex of $S$ lies in $D$.

In a phase, $L$ and $R$ are the left and right vertices of the paths found so far.
