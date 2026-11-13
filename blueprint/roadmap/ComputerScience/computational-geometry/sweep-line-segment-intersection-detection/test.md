# Intersection test for two input segments

Given $n$ segments in the plane over a
linearly ordered field, each given by its two endpoints, and indices $i, j < n$, this runs CLRS
`SEGMENTS-INTERSECT` on the left and right endpoints of segment $i$ and the left and right
endpoints of segment $j$. It returns that procedure's Boolean answer together with its cost in
`DIRECTION` and `ON-SEGMENT` evaluations.
