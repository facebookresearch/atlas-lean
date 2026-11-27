# The in-circle test as a lifted orientation test

Let $p, q, r, s$ be distinct points of $\mathbb{R}^2$ with $p, q, r$ not on a line, and write $u^\uparrow = (u_x, u_y, u_x^2 + u_y^2)$ for the lift of a point $u$ to the paraboloid $z = x^2 + y^2$. Then $s$ lies in the interior of the circumcircle of $pqr$ if and only if $s^\uparrow$ lies strictly below the plane through $p^\uparrow$, $q^\uparrow$ and $r^\uparrow$. Equivalently, for $p, q, r$ in counterclockwise order, $s$ is inside the circumcircle exactly when the $4 \times 4$ determinant with rows $(u_x, u_y, u_x^2 + u_y^2, 1)$ for $u = p, q, r, s$ is positive.

## Sources

- D. M. Mount, *CMSC 754: Computational Geometry*, lecture notes, University of Maryland, Spring 2020, <https://www.cs.umd.edu/class/spring2020/cmsc754/Lects/cmsc754-spring2020-lects.pdf>: Lecture 35, the lemma relating the circumcircle of $pqr$ to the plane through the lifted points, and Lecture 13, "Incircle Test"
