# A collinear point in the bounding box lies on the segment

Let $K$ be a linearly ordered
field, write $(u_1, u_2) \times (v_1, v_2) = u_1 v_2 - v_1 u_2$ for the cross product on $K^2$, and
let $p, q, r \in K^2$. If $r$ is collinear with $p$ and $q$, that is, the direction
$(r - p) \times (q - p)$ is zero, and ON-SEGMENT$(p, q, r)$ is true, that is, $r$ lies in the
bounding box of $p$ and $q$, then $r$ lies on the closed segment from $p$ to $q$.

This is the fact behind CLRS's use of ON-SEGMENT.
