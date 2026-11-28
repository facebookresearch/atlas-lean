# Illumination in a mirrored room

In a polygonal room $R$, a point $s$ illuminates a point $t$ when $s = t$ or there is a light path from $s$ to $t$ in $R$ with some finite number $r \ge 0$ of reflections.

A light path from $s$ to $t$ is a finite sequence $s = x_0, x_1, \dots, x_r, x_{r+1} = t$ ($r \ge 0$ reflections) with consecutive points distinct and every open leg $(x_i, x_{i+1})$ inside $R^\circ$, such that each reflection point $x_i$ ($1 \le i \le r$) lies on the frontier of $R^\circ$, the frontier near $x_i$ coincides with a line through $x_i$ with nonzero direction $w_i$, and the outgoing unit direction is the reflection of the incoming unit direction in that line: $u(x_i, x_{i+1}) = 2\frac{\langle u(x_{i-1}, x_i), w_i\rangle}{\langle w_i, w_i\rangle} w_i - u(x_{i-1}, x_i)$, where $u(a, b) = (b - a)/\lVert b - a \rVert$. In particular light reaching a corner of the room is absorbed.
