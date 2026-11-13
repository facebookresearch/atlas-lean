# Blelloch's scan on lists

Let $M$ be a monoid. For a natural number $k$ and a list
$xs = (x_0, x_1, \dots)$ in $M$, the list scan $L_k(xs)$ is defined by recursion on $k$:
$L_0(xs)$ is the one-element list $(1)$, and $L_{k+1}(xs)$ is obtained from the list scan
$z = L_k(p)$ of the pair products $p = (x_0 x_1, x_2 x_3, \dots)$ of $xs$ (a trailing unpaired
entry is dropped) by interleaving: $L_{k+1}(xs) = (z_0, z_0 x_0, z_1, z_1 x_2, \dots)$, where
each $z_i$ is followed by $z_i x_{2i}$ and the list stops at the first $i$ for which $z_i$ or
$x_{2i+1}$ does not exist.

On a list of length $2^k$ this takes $O(2^k)$ time.
