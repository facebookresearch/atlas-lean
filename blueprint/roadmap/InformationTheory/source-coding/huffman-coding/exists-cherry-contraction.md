# Contracting a deepest sibling pair

Let $T$ be a weight tree of height $h \ge 1$. Then
there are real numbers $x$ and $y$, a multiset $M$ of real numbers and a real number $c$ such that
the multiset of leaf weights of $T$ is $\{x, y\} + M$, the path cost of $T$ is $c + hx + hy$, and
for every real number $z$ there is a weight tree $T'$ of height at most $h$ whose multiset of leaf
weights is $\{z\} + M$ and whose path cost is $c + (h - 1)z$.

In the proof, $x$ and $y$ are the weights of a deepest pair of sibling leaves of $T$, and $T'$
replaces that pair by a single leaf of weight $z$.
