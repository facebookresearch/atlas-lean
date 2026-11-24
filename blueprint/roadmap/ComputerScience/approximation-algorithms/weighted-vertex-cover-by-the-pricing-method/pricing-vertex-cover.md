# Pricing method for weighted vertex cover

Given rational weights $w$ on a finite vertex
set $V$ and a list of edges (ordered pairs of vertices), run the pricing scan on the list
starting from residual weights $w$ and total price $0$, then return the set of vertices whose
final residual weight is $0$. On top of the cost of the scan, the selection costs $|V|$ time
units.
