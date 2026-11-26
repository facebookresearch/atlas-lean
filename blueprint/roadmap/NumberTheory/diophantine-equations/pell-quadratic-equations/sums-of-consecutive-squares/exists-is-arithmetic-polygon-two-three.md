# The $3$-$4$-$5$ right triangle is an arithmetic polygon without reflex angles

An arithmetic polygon with parameters $a \ge 0$ and $N \ge 3$ is a closed polygon in the plane with distinct vertices $v_0, v_1, \dots, v_{N-1}$, indices taken modulo $N$, whose special vertex is $O = v_0$, such that

- side $k$, joining $v_k$ to $v_{k+1}$, has length $a + 1 + k$ for $0 \le k < N$;
- for each side, $O - v_k$ or $O - v_{k+1}$ is orthogonal to $v_{k+1} - v_k$, that is, a line perpendicular to the side passes through $O$ and one of its endpoints;
- consecutive sides are never parallel, so no angle is $0$ or $\pi$.

There is such a polygon with $a = 2$ and $N = 3$, so with sides $3$, $4$ and $5$ in this order from $O$, that is moreover not self-intersecting (two distinct sides meet at most in common endpoints) and has no reflex angle: at no vertex does the turn from one side to the next have sign opposite to the orientation of the polygon. For instance, the right triangle with vertices $0$, $3$ and $3 + 4i$ in the complex plane is such a polygon.

## Sources

- Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of Consecutive Squares*, INTEGERS 26 (2026), Article A1, Definition 1, Section 1 and the proof of Theorem 4.
