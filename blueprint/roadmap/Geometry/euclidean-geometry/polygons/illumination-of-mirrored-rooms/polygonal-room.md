# Polygonal rooms

A polygonal room consists of a number $k \ge 3$ of sides, pairwise distinct vertices $v_0, \dots, v_{k-1} \in \mathbb{R}^2$ listed in cyclic order, and an open floor $R^\circ \subseteq \mathbb{R}^2$ such that:

- $R^\circ$ is open, nonempty, connected and bounded;
- $R^\circ$ is regular open: the interior of its closure is $R^\circ$;
- the frontier of $R^\circ$ is the union of the closed walls $[v_i, v_{i+1}]$, indices taken mod $k$;
- for $i \ne j$, the walls $[v_i, v_{i+1}]$ and $[v_j, v_{j+1}]$ meet only in points that are endpoints of both.

The closure of $R^\circ$ is the physical room with its walls. Redundant collinear vertices that subdivide a straight wall are allowed.
