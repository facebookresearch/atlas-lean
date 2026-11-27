# Residual sum of squares in archetypal analysis

Let $E$ be a real inner product space, $x_1, \dots, x_n \in E$ data points and
$z_1, \dots, z_p \in E$ archetypes, with convex hull $C$. The residual sum of squares is
$\mathrm{RSS}(z) = \sum_{i=1}^n d(x_i, C)^2$: each data point is replaced by the closest point of
the convex hull of the archetypes. This is only meaningful for $p \ge 1$: for $p = 0$ the hull is
empty, the distance to the empty set is $0$ by convention, so the residual sum of squares is $0$
and must not be read as a perfect fit.
