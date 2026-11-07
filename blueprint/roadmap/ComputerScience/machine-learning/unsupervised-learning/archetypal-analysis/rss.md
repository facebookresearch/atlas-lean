# Residual sum of squares in archetypal analysis

The residual sum of squares of archetypes `z` for the data `x`: each data point is
replaced by the closest point of the convex hull of the archetypes. This is only meaningful
for `0 < p`: for `p = 0` the hull is empty and `infDist` to the empty set is `0` by
convention, so `rss` is `0` vacuously and must not be read as a perfect fit.
