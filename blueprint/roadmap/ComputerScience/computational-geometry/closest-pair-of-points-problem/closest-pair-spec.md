# Correctness of divide-and-conquer closest pair

Let $K$ be a linearly ordered field and let
$ps$ be a list of at least two points in $K^2$. Then the divide-and-conquer closest-pair algorithm
returns a value $\delta$, and $\delta$ is the least squared distance between two entries of $ps$
at different positions: some two entries at different positions have squared distance $\delta$,
and any two entries at different positions have squared distance at least $\delta$.

This is the correctness of CLRS Section 33.4, with distances compared squared.
