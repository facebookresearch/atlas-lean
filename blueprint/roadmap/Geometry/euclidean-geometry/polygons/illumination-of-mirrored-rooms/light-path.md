# Light paths in a mirrored room

Let $R$ be a polygonal room with open floor $R^\circ$ and let $s, t \in \mathbb{R}^2$. A light path from $s$ to $t$ in $R$ consists of a number $r \ge 0$ of reflections, points $x_0, x_1, \dots, x_{r+1} \in \mathbb{R}^2$ and wall directions $w_1, \dots, w_r$ such that:

- $x_0 = s$ and $x_{r+1} = t$;
- $x_i \ne x_{i+1}$ and the open segment $(x_i, x_{i+1})$ lies in $R^\circ$ for $0 \le i \le r$;
- for $1 \le i \le r$, $w_i \ne 0$, $x_i$ lies on the frontier of $R^\circ$, and for some $\varepsilon > 0$ the frontier within distance $\varepsilon$ of $x_i$ is exactly the line $\{x_i + \tau w_i : \tau \in \mathbb{R}\}$ within that distance;
- for $1 \le i \le r$, the specular law holds:

    $$u(x_i, x_{i+1}) = 2\,\frac{\langle u(x_{i-1}, x_i), w_i\rangle}{\langle w_i, w_i\rangle}\, w_i - u(x_{i-1}, x_i), \qquad u(a, b) = \frac{b - a}{\lVert b - a \rVert}.$$

Reflections happen only where the wall is locally straight, so light reaching a corner is absorbed.
