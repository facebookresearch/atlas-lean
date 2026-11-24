# Pricing scan

Given rational residual weights $r$ on the vertices, a rational total
price $P$ and a list of edges (ordered pairs of vertices), the pricing scan processes the
edges in order: an edge $(u, v)$ has price $\delta = \min(r(u), r(v))$, which is subtracted
from the residual weight of $u$ and of $v$ (once if $u = v$) and added to the total price.
The result is the final pair of residual weights and total price, and the scan costs one
time unit per edge.
