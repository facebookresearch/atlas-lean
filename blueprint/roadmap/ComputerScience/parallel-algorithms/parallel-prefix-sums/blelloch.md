# Blelloch's scan

Let $M$ be a monoid. For a natural number $k$ and a sequence
$x = (x_0, x_1, \dots)$ in $M$, the scan $B_k(x)$ is the sequence in $M$ defined by recursion
on $k$: $B_0(x)$ is constantly $1$, and $B_{k+1}(x)$ is obtained from the scan $y = B_k(p)$ of
the pair products $p_i = x_{2i} x_{2i+1}$ by setting $B_{k+1}(x)_{2i} = y_i$ and
$B_{k+1}(x)_{2i+1} = y_i x_{2i}$ for every $i$.
