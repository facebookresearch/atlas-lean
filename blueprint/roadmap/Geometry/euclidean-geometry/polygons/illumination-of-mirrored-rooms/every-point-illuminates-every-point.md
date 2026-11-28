# Mirrored room illumination: every point lights every point

Conjecture: in every polygonal room with perfectly mirrored walls, every point of the open floor illuminates every point of the open floor. That is, for every polygonal room $R$ and all $s, t \in R^\circ$, either $s = t$ or there is a light path from $s$ to $t$.

A polygonal room $R$ has vertices $v_0, \dots, v_{k-1}$ ($k \ge 3$, pairwise distinct) in cyclic order and an open floor $R^\circ \subseteq \mathbb{R}^2$ that is nonempty, open, connected and bounded, equal to the interior of its closure, and whose frontier is the union of the closed walls $[v_i, v_{i+1}]$ (indices mod $k$), any two of which meet only in common endpoints.

A light path from $s$ to $t$ is a finite sequence $s = x_0, x_1, \dots, x_r, x_{r+1} = t$ ($r \ge 0$ reflections) with consecutive points distinct and every open leg $(x_i, x_{i+1})$ inside $R^\circ$, such that each reflection point $x_i$ ($1 \le i \le r$) lies on the frontier of $R^\circ$, the frontier near $x_i$ coincides with a line through $x_i$ with nonzero direction $w_i$, and the outgoing unit direction is the reflection of the incoming unit direction in that line: $u(x_i, x_{i+1}) = 2\frac{\langle u(x_{i-1}, x_i), w_i\rangle}{\langle w_i, w_i\rangle} w_i - u(x_{i-1}, x_i)$, where $u(a, b) = (b - a)/\lVert b - a \rVert$. In particular light reaching a corner of the room is absorbed. It is false; the refutation is [Tokarsky: mirrored rooms not illuminable from every point](every-point-illuminates-every-point-refu.md).

## Sources

- D. Eppstein, The Geometry Junkyard: Open Problems, item Mirrored room illumination, https://ics.uci.edu/~eppstein/junkyard/mirror.html
- J. O'Rourke, Art Gallery Theorems and Algorithms (1987), pp. 265-266
