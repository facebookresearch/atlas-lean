# Leftmost key of a tree

Given a default value $d$ and a binary tree $T$ with cached
heights, the leftmost key of $T$ with default $d$ is $d$ when $T$ is empty; when $T$ has left
subtree $L$ and root key $k$, it is the leftmost key of $L$ with default $k$. Thus for a
nonempty tree it is the key of the node reached from the root by following left children as
far as possible, and it does not depend on $d$.
