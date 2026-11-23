# Southeast paths

A point of the quarter plane is a pair $(a, b) \in \mathbb{N}^2$, with $a$
the horizontal coordinate and $b$ the height. Let $p$ and $q$ be points of the quarter plane. A
southeast path from $p$ to $q$ is a list $v = [v_0, v_1, \dots, v_m]$ of points of the quarter
plane, for some $m \in \mathbb{N}$, with $v_0 = p$, $v_m = q$, and, for each $1 \le t \le m$,
either $v_t = v_{t-1} + (1, 0)$ (an east step) or $v_{t-1} = v_t + (0, 1)$ (a south step).

For $m = 0$ the path is the single point $[p]$, which is a southeast path from $p$ to $q$ exactly
when $p = q$. The empty list is not a southeast path. Writing $p = (a, b)$ and $q = (c, d)$, a
southeast path from $p$ to $q$ exists exactly when $a \le c$ and $d \le b$, and then
$m = (c - a) + (b - d)$.
