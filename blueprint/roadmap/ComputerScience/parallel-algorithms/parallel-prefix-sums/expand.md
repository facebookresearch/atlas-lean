# Interleaving step of Blelloch's list scan

Let $M$ be a monoid. For lists
$z = (z_0, z_1, \dots)$ and $x = (x_0, x_1, \dots)$ in $M$, the expansion of $z$ along $x$ is
the list $(z_0, z_0 x_0, z_1, z_1 x_2, z_2, z_2 x_4, \dots)$: each $z_i$ is followed by
$z_i x_{2i}$, and the list stops at the first $i$ for which $z_i$ or $x_{2i+1}$ does not
exist.
